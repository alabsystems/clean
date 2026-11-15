// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(43))
}
fn fixture() -> Module {
    let mut module = Module::new("drop-index");
    module.drop_glue = vec![
        DropGlueEntry {
            ty: Ty::Struct(StructId::new(3)),
            glue: FuncId::new(11),
        },
        DropGlueEntry {
            ty: Ty::Tuple(vec![Ty::Struct(StructId::new(3)), Ty::Bool]),
            glue: FuncId::new(12),
        },
        DropGlueEntry {
            ty: Ty::Struct(StructId::new(3)),
            glue: FuncId::new(11),
        },
    ];
    module
}
#[test]
fn observed_lookup_preserves_source_and_unique_missing_duplicate_semantics() {
    let module = fixture();
    let ordinary = module.drop_glue_index();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let index = module
        .drop_glue_index_observed(&mut session, site())
        .unwrap();
    assert!(core::ptr::eq(index.source_module(), &module));
    for ty in [
        Ty::Struct(StructId::new(3)),
        Ty::Tuple(vec![Ty::Struct(StructId::new(3)), Ty::Bool]),
        Ty::Char,
        Ty::U32,
    ] {
        assert_eq!(
            index.resolve(&ty, &mut session, site()).unwrap(),
            ordinary.resolve(&ty)
        );
    }
    for id in [FuncId::new(11), FuncId::new(12), FuncId::new(13)] {
        assert_eq!(
            index.is_glue(id, &mut session, site()).unwrap(),
            ordinary.is_glue(id)
        );
    }
    assert_eq!(
        index.is_empty(&mut session, site()).unwrap(),
        ordinary.is_empty()
    );
}
#[test]
fn original_cumulative_work_and_interior_stop_cover_real_table_and_type_walks() {
    let module = fixture();
    let ty = Ty::Tuple(vec![Ty::Struct(StructId::new(3)), Ty::Bool]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let index = module
        .drop_glue_index_observed(&mut session, site())
        .unwrap();
    index.resolve(&ty, &mut session, site()).unwrap();
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = module
            .drop_glue_index_observed(&mut session, site())
            .and_then(|index| index.resolve(&ty, &mut session, site()));
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    }
    let mut observer = Observer {
        cap: Some(measured.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let index = module
        .drop_glue_index_observed(&mut session, site())
        .unwrap();
    index.resolve(&ty, &mut session, site()).unwrap();
    assert_eq!(
        index.resolve(&ty, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
