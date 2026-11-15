// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: ordinary Constant Float Debug is the exact parity oracle.
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncId};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("float original stop");
        }
        if self.cleanup
            && self.stop.is_some_and(|n| self.events.len() > n)
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(719),
        block: BlockId::new(31),
        instruction_index: 43,
    })
}
fn run(v: f64) -> (String, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = Constant::Float(v).display_observed(&mut s, site()).unwrap();
    assert_eq!(text, Constant::Float(v).to_string());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (text, o)
}
#[test]
fn exact_special_tokens_signed_zero_and_ordinary_whole_fractional_exponent_spelling() {
    for (v, expected) in [
        (0.0, "0.0"),
        (-0.0, "-0.0"),
        (1.0, "1.0"),
        (-42.0, "-42.0"),
        (1.25, "1.25"),
        (1e300, "1e300"),
        (1e-300, "1e-300"),
        (f64::INFINITY, "inf"),
        (f64::NEG_INFINITY, "-inf"),
        (f64::NAN, "NaN"),
        (f64::from_bits(0xfff0_0000_0000_0001), "NaN"),
    ] {
        assert_eq!(run(v).0, expected);
    }
}
#[derive(Default)]
struct Counting {
    calls: usize,
}
impl ExecutionObserver for Counting {
    type Refusal = ();
    fn admit(&mut self, _: ExecutionProgress) -> Result<(), ()> {
        self.calls += 1;
        Ok(())
    }
}
fn parity(v: f64) {
    let mut o = Counting::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = Constant::Float(v).display_observed(&mut s, site()).unwrap();
    assert_eq!(
        text,
        Constant::Float(v).to_string(),
        "bits {:016x}",
        v.to_bits()
    );
    if v.is_finite() {
        assert_eq!(text.parse::<f64>().unwrap().to_bits(), v.to_bits());
    }
    assert!(s.first_refusal().is_none());
}
#[test]
fn normal_subnormal_maximum_and_every_binary_exponent_transition_match_pinned_std() {
    for exponent in 0u64..=0x7fe {
        let base = exponent << 52;
        for bits in [
            base,
            base.saturating_sub(1),
            base + 1,
            base | ((1u64 << 52) - 1),
        ] {
            parity(f64::from_bits(bits));
            parity(f64::from_bits(bits | (1u64 << 63)));
        }
    }
}
#[test]
fn fixed_seed_mantissas_and_decimal_debug_policy_boundaries_match_ordinary() {
    let mut bits = 0x1234_5678_9abc_def0u64;
    for _ in 0..1024 {
        bits = bits.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        parity(f64::from_bits(bits));
    }
    for v in [1e-4f64, 1e16, 1e-3, 1e15, 0.1, 1.2345678901234567] {
        for bits in [v.to_bits() - 1, v.to_bits(), v.to_bits() + 1] {
            parity(f64::from_bits(bits));
        }
    }
}
#[test]
fn every_actual_small_float_callback_refuses_with_exact_original_cause_and_no_partial_result() {
    let (_, base) = run(-1.25);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            cleanup: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            Constant::Float(-1.25).display_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "float original stop");
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn same_original_work_copy_site_zero_fuel_and_sticky_refusal_span_calls() {
    let (_, base) = run(1.25);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            Constant::Float(1.25)
                .display_observed(&mut s, site())
                .unwrap(),
            "1.25"
        );
        assert_eq!(
            Constant::Float(1.25).display_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            Constant::Float(1.25).display_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), 0);
        assert!(o.events.iter().all(|e| e.site == site()));
    }
}
#[test]
fn actual_power_scaling_word_interior_is_refusable_after_held_negative_prefix() {
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut output = String::new();
    write(-f64::from_bits(1), &mut output, &mut w).unwrap();
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 3
                && e.copy_bytes == 3 * size_of::<u64>() + size_of::<u32>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut output = String::new();
    assert_eq!(
        write(-f64::from_bits(1), &mut output, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(output, "-");
    w.retire(take(&mut output));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(output.capacity(), 0);
}
#[test]
fn numeric_child_return_and_partial_fraction_text_remain_in_parent_custody() {
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut output = "prior: ".to_string();
    write(1.25, &mut output, &mut w).unwrap();
    // Refuse the actual fractional-copy admission, after the integral text and
    // decimal point were appended. No opaque formatter or alternate entry.
    let stop = base
        .events
        .iter()
        .enumerate()
        .rfind(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 2 && e.copy_bytes == 2)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut output = "prior: ".to_string();
    assert_eq!(
        write(1.25, &mut output, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(output, "prior: 1.");
    w.retire(take(&mut output));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(output.capacity(), 0);
}
#[test]
fn fixed_word_capacity_rejects_shift_overflow_and_actual_scalar_admission_before_initialization() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(matches!(
        big::Big::new(1, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    ));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut n = big::Big::new(1, &mut w).unwrap();
    assert!(matches!(
        n.shift(1280, &mut w),
        Err(ObservedValueError::CapacityOverflow)
    ));
    assert_eq!(
        n.compare(&big::Big::new(1, &mut w).unwrap(), &mut w)
            .unwrap(),
        Ordering::Equal
    );
}
