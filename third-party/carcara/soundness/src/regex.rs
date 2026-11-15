// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB regular languages, decided by Brzozowski derivatives on short strings.

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Re {
    None,
    Eps,
    AllChar,
    /// A single character in the inclusive range.
    Range(u32, u32),
    Lit(Vec<u32>),
    Concat(Vec<Re>),
    Union(Vec<Re>),
    Inter(Vec<Re>),
    Star(Box<Re>),
    Comp(Box<Re>),
    /// `lo..=hi` repetitions (empty when `lo > hi`).
    Loop(Box<Re>, u32, u32),
}

impl Re {
    pub fn all() -> Re {
        Re::Star(Box::new(Re::AllChar))
    }

    pub fn nullable(&self) -> bool {
        match self {
            Re::None | Re::AllChar | Re::Range(..) => false,
            Re::Eps | Re::Star(_) => true,
            Re::Lit(s) => s.is_empty(),
            Re::Concat(rs) => rs.iter().all(Re::nullable),
            Re::Union(rs) => rs.iter().any(Re::nullable),
            Re::Inter(rs) => rs.iter().all(Re::nullable),
            Re::Comp(r) => !r.nullable(),
            Re::Loop(r, lo, hi) => lo <= hi && (*lo == 0 || r.nullable()),
        }
    }

    pub fn deriv(&self, c: u32) -> Re {
        match self {
            Re::None | Re::Eps => Re::None,
            Re::AllChar => Re::Eps,
            Re::Range(a, b) => {
                if *a <= c && c <= *b {
                    Re::Eps
                } else {
                    Re::None
                }
            }
            Re::Lit(s) => match s.split_first() {
                Some((&first, rest)) if first == c => Re::Lit(rest.to_vec()),
                _ => Re::None,
            },
            Re::Concat(rs) => match rs.split_first() {
                None => Re::None,
                Some((first, rest)) => {
                    let rest_re = Re::Concat(rest.to_vec());
                    let mut alts = vec![Re::Concat(
                        std::iter::once(first.deriv(c))
                            .chain(rest.iter().cloned())
                            .collect(),
                    )];
                    if first.nullable() {
                        alts.push(rest_re.deriv(c));
                    }
                    Re::Union(alts)
                }
            },
            Re::Union(rs) => Re::Union(rs.iter().map(|r| r.deriv(c)).collect()),
            Re::Inter(rs) => Re::Inter(rs.iter().map(|r| r.deriv(c)).collect()),
            Re::Star(r) => Re::Concat(vec![r.deriv(c), self.clone()]),
            Re::Comp(r) => Re::Comp(Box::new(r.deriv(c))),
            Re::Loop(r, lo, hi) => {
                if lo > hi || *hi == 0 {
                    Re::None
                } else {
                    Re::Concat(vec![
                        r.deriv(c),
                        Re::Loop(r.clone(), lo.saturating_sub(1), hi - 1),
                    ])
                }
            }
        }
    }

    pub fn matches(&self, s: &[u32]) -> bool {
        let mut cur = self.clone();
        for &c in s {
            cur = cur.deriv(c).simplify();
        }
        cur.nullable()
    }

    fn simplify(self) -> Re {
        match self {
            Re::Concat(rs) => {
                let rs: Vec<Re> = rs
                    .into_iter()
                    .map(Re::simplify)
                    .filter(|r| *r != Re::Eps && *r != Re::Lit(Vec::new()))
                    .collect();
                if rs.iter().any(|r| *r == Re::None) {
                    Re::None
                } else if rs.is_empty() {
                    Re::Eps
                } else if rs.len() == 1 {
                    rs.into_iter().next().unwrap()
                } else {
                    Re::Concat(rs)
                }
            }
            Re::Union(rs) => {
                let mut out: Vec<Re> = Vec::new();
                for r in rs.into_iter().map(Re::simplify) {
                    if r != Re::None && !out.contains(&r) {
                        out.push(r);
                    }
                }
                match out.len() {
                    0 => Re::None,
                    1 => out.pop().unwrap(),
                    _ => Re::Union(out),
                }
            }
            Re::Inter(rs) => {
                let rs: Vec<Re> = rs.into_iter().map(Re::simplify).collect();
                if rs.iter().any(|r| *r == Re::None) {
                    Re::None
                } else if rs.len() == 1 {
                    rs.into_iter().next().unwrap()
                } else {
                    Re::Inter(rs)
                }
            }
            Re::Comp(r) => Re::Comp(Box::new(r.simplify())),
            other => other,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Re;

    fn s(x: &str) -> Vec<u32> {
        x.chars().map(|c| c as u32).collect()
    }

    #[test]
    fn basic_languages() {
        let ab = Re::Concat(vec![Re::Lit(s("a")), Re::Star(Box::new(Re::Lit(s("b"))))]);
        assert!(ab.matches(&s("a")));
        assert!(ab.matches(&s("abbb")));
        assert!(!ab.matches(&s("ba")));
        assert!(Re::Comp(Box::new(ab.clone())).matches(&s("ba")));
        let lp = Re::Loop(Box::new(Re::Lit(s("a"))), 2, 3);
        assert!(!lp.matches(&s("a")));
        assert!(lp.matches(&s("aa")));
        assert!(lp.matches(&s("aaa")));
        assert!(!lp.matches(&s("aaaa")));
        assert!(!Re::Loop(Box::new(Re::Eps), 3, 2).matches(&s("")));
        assert!(Re::all().matches(&s("xyz")));
        assert!(Re::Inter(vec![Re::all(), Re::AllChar]).matches(&s("x")));
    }
}
