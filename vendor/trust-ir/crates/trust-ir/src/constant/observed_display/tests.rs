// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored controls, UNRUN until an independent native owner executes.
use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("original stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(91))
}
fn text(value: &Constant) -> (String, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let text = value.display_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (text, observer)
}
fn mixed() -> Constant {
    Constant::Record(vec![
        (
            "λ field\n".into(),
            Constant::Aggregate(vec![Constant::Int(-3), Constant::Bool(true)]),
        ),
        (
            "bytes".into(),
            Constant::Bytes {
                data: vec![0, 15, 16, 255],
                utf8: false,
            },
        ),
        (
            "closure".into(),
            Constant::Closure {
                func: FuncId::new(2),
                captures: vec![Constant::FnDef(FuncId::new(4))],
            },
        ),
    ])
}
#[test]
fn every_nonfloat_carrier_matches_actual_ordinary_display_spelling() {
    let values = vec![
        Constant::Int(i128::MIN),
        Constant::Int(i128::MAX),
        Constant::Int(0),
        Constant::U128(0),
        Constant::U128(u128::MAX),
        Constant::Bool(false),
        Constant::Bytes {
            data: vec![0, 1, 15, 16, 255],
            utf8: true,
        },
        Constant::Aggregate(vec![]),
        Constant::Array(vec![]),
        Constant::Vector(vec![Constant::Int(1), Constant::Int(2)]),
        Constant::Sequence(vec![Constant::PhantomData]),
        Constant::Set(vec![Constant::Uninit]),
        Constant::Record(vec![]),
        Constant::Closure {
            func: FuncId::new(u32::MAX),
            captures: vec![],
        },
        Constant::SymbolAddr {
            symbol: "raw λ\n< >".into(),
            addend: i64::MIN,
        },
        Constant::SymbolAddr {
            symbol: "empty-addend".into(),
            addend: 0,
        },
        Constant::SymbolAddr {
            symbol: "positive".into(),
            addend: i64::MAX,
        },
        mixed(),
    ];
    for value in values {
        let (actual, observer) = text(&value);
        assert_eq!(actual, value.to_string());
        assert!(observer.events.iter().all(|event| event.site == site()));
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::Publication
        );
    }
    assert_eq!(text(&Constant::Aggregate(vec![])).0, "{  }");
    assert_eq!(
        text(&Constant::Closure {
            func: FuncId::new(1),
            captures: vec![]
        })
        .0,
        "closure<func.1>{ }"
    );
}
#[test]
fn maximum_length_splat_is_spelled_once_without_expanding_its_length() {
    let value = Constant::Splat {
        elem: Box::new(Constant::Int(-7)),
        len: u64::MAX,
    };
    let (actual, observer) = text(&value);
    assert_eq!(actual, value.to_string());
    assert_eq!(actual, "splat[ -7; 18446744073709551615 ]");
    assert!(observer.work < 10_000);
}
#[test]
fn byte_hex_and_unicode_text_walk_actual_chunk_interiors() {
    for utf8 in [false, true] {
        let value = Constant::Bytes {
            data: (0..=255).cycle().take(4097).collect(),
            utf8,
        };
        let (actual, observer) = text(&value);
        assert_eq!(actual, value.to_string());
        assert!(
            observer
                .events
                .iter()
                .filter(|event| event.work == 1 && event.copy_bytes == 2)
                .count()
                >= 4097
        );
    }
    let value = Constant::Record(vec![(
        "界".repeat(1500),
        Constant::SymbolAddr {
            symbol: "λ".repeat(3000),
            addend: -1,
        },
    )]);
    let (actual, observer) = text(&value);
    assert_eq!(actual, value.to_string());
    assert!(
        observer
            .events
            .iter()
            .filter(|event| event.work == 1023 && event.copy_bytes == 1023)
            .count()
            >= 4
    );
}
#[test]
fn deep_splat_walk_is_iterative_and_input_remains_caller_owned() {
    let depth = 20_000;
    let mut value = Constant::Bool(true);
    for _ in 0..depth {
        value = Constant::Splat {
            elem: Box::new(value),
            len: 2,
        };
    }
    let (actual, _) = text(&value);
    assert_eq!(actual.len(), depth * 12 + 4);
    assert!(actual.starts_with("splat[ splat[ "));
    assert!(actual.ends_with("; 2 ]; 2 ]"));
    // The helper borrows the input: this fixture explicitly consumes its own
    // deep boxes instead of recursively dropping them in the test harness.
    loop {
        match value {
            Constant::Splat { elem, .. } => value = *elem,
            Constant::Bool(true) => break,
            _ => panic!("fixture changed"),
        }
    }
}
#[test]
fn every_float_in_a_partially_spelled_container_matches_the_ordinary_complete_result() {
    for float in [
        0.0,
        -0.0,
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MIN_POSITIVE,
    ] {
        let value = Constant::Aggregate(vec![Constant::Int(1), Constant::Float(float)]);
        let (actual, observer) = text(&value);
        assert_eq!(actual, value.to_string());
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::Publication
        );
    }
}
