// Copyright 2026 Andrew Yates; algorithm adapted from the Rust project contributors.
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Burger–Dybvig Dragon shortest mode, as pinned core's exact fallback.
use super::*;
use big::Big;
struct Decoded {
    mant: u64,
    minus: u64,
    plus: u64,
    exp: i16,
    inclusive: bool,
}
pub(super) struct Digits {
    pub(super) bytes: [u8; 18],
    pub(super) len: usize,
    pub(super) exp: i16,
}
fn decode<O: ExecutionObserver>(bits: u64, work: &mut Work<'_, '_, O>) -> R<Decoded> {
    work.admit(20, size_of::<Decoded>())?;
    let exponent = ((bits >> 52) & 0x7ff) as i16;
    let fraction = bits & ((1u64 << 52) - 1);
    let mant = if exponent == 0 {
        fraction << 1
    } else {
        fraction | (1u64 << 52)
    };
    let exp = exponent - 1075;
    let inclusive = mant & 1 == 0;
    Ok(if exponent == 0 {
        Decoded {
            mant,
            minus: 1,
            plus: 1,
            exp,
            inclusive,
        }
    } else if mant == 1u64 << 52 {
        Decoded {
            mant: mant << 2,
            minus: 1,
            plus: 2,
            exp: exp - 2,
            inclusive,
        }
    } else {
        Decoded {
            mant: mant << 1,
            minus: 1,
            plus: 1,
            exp: exp - 1,
            inclusive,
        }
    })
}
pub(super) fn shortest<O: ExecutionObserver>(bits: u64, work: &mut Work<'_, '_, O>) -> R<Digits> {
    let result = generate(bits, work);
    // All numeric scratch is fixed inline integers, with no owned heap or
    // recursive Drop. This poll keeps a cleanup refusal in the same owner.
    work.session.retirement_step(work.site, 1);
    match result {
        Ok(digits) if work.session.first_refusal().is_none() => Ok(digits),
        Ok(_) => Err(ObservedValueError::AdmissionRefused),
        Err(error) => Err(work.terminal(error)),
    }
}
fn generate<O: ExecutionObserver>(bits: u64, work: &mut Work<'_, '_, O>) -> R<Digits> {
    let d = decode(bits, work)?;
    if d.mant == 0 {
        return Err(ObservedValueError::InvalidRange);
    }
    work.admit(8, size_of::<Digits>() + 3 * size_of::<i64>())?;
    let nbits = 64 - (d.mant + d.plus - 1).leading_zeros() as i64;
    let mut k = (((nbits + i64::from(d.exp)) * 1_292_913_986) >> 32) as i16;
    work.admit(6, size_of::<bool>())?;
    if d.mant >= (1u64 << 55) || !(-1076..=970).contains(&d.exp) || !(-324..=309).contains(&k) {
        return Err(ObservedValueError::InvalidRange);
    }
    let rounding = if d.inclusive {
        Ordering::Greater
    } else {
        Ordering::Equal
    };
    let mut mant = Big::new(d.mant, work)?;
    let mut minus = Big::new(d.minus, work)?;
    let mut plus = Big::new(d.plus, work)?;
    let mut scale = Big::new(1, work)?;
    if d.exp < 0 {
        scale.shift(d.exp.unsigned_abs() as usize, work)?;
    } else {
        mant.shift(d.exp as usize, work)?;
        minus.shift(d.exp as usize, work)?;
        plus.shift(d.exp as usize, work)?;
    }
    if k >= 0 {
        scale.pow10(k as usize, work)?;
    } else {
        mant.pow10(k.unsigned_abs() as usize, work)?;
        minus.pow10(k.unsigned_abs() as usize, work)?;
        plus.pow10(k.unsigned_abs() as usize, work)?;
    }
    let mut high = mant.copy(work)?;
    high.add(&plus, work)?;
    if scale.compare(&high, work)? < rounding {
        k += 1;
    } else {
        mant.mul(10, work)?;
        minus.mul(10, work)?;
        plus.mul(10, work)?;
    }
    let mut scale2 = scale.copy(work)?;
    scale2.shift(1, work)?;
    let mut scale4 = scale.copy(work)?;
    scale4.shift(2, work)?;
    let mut scale8 = scale.copy(work)?;
    scale8.shift(3, work)?;
    work.admit(18, size_of::<Digits>())?;
    let mut output = Digits {
        bytes: [0; 18],
        len: 0,
        exp: k,
    };
    loop {
        // Prepay the four borrowed divisors before their fixed tuple array is
        // constructed, as well as this iteration's flags and digit cell.
        work.admit(
            6,
            2 * size_of::<bool>() + size_of::<u8>() + size_of::<[(u8, &Big); 4]>(),
        )?;
        // binary64 needs at most 17 significant digits. One further cell is
        // reserved only for core's documented all-nine rounding carry.
        if output.len >= 17 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut digit = 0u8;
        for (amount, divisor) in [(8, &scale8), (4, &scale4), (2, &scale2), (1, &scale)] {
            work.admit(1, size_of::<u8>())?;
            if mant.compare(divisor, work)? != Ordering::Less {
                mant.sub(divisor, work)?;
                digit += amount;
            }
        }
        work.admit(2, size_of::<u8>() + size_of::<usize>())?;
        if digit >= 10 {
            return Err(ObservedValueError::InvalidRange);
        }
        output.bytes[output.len] = b'0' + digit;
        output.len += 1;
        let down = mant.compare(&minus, work)? < rounding;
        high = mant.copy(work)?;
        high.add(&plus, work)?;
        let up = scale.compare(&high, work)? < rounding;
        if down || up {
            if up
                && (!down || {
                    mant.shift(1, work)?;
                    mant.compare(&scale, work)? != Ordering::Less
                })
            {
                output.round(work)?;
            }
            return Ok(output);
        }
        mant.mul(10, work)?;
        minus.mul(10, work)?;
        plus.mul(10, work)?;
    }
}
impl Digits {
    fn round<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let mut at = self.len;
        while at != 0 {
            work.admit(2, size_of::<u8>() + size_of::<usize>())?;
            at -= 1;
            if self.bytes[at] != b'9' {
                self.bytes[at] += 1;
                return Ok(());
            }
            self.bytes[at] = b'0';
        }
        work.admit(
            3,
            2 * size_of::<u8>() + size_of::<usize>() + size_of::<i16>(),
        )?;
        self.bytes[0] = b'1';
        *self
            .bytes
            .get_mut(self.len)
            .ok_or(ObservedValueError::CapacityOverflow)? = b'0';
        self.len += 1;
        self.exp += 1;
        Ok(())
    }
}
