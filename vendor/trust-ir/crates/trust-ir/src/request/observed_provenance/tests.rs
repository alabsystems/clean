// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::interpret::InterpretOptions;
use crate::{BlockId, FuncTyId, Function, ModuleImport, ProofDigest};

mod parity;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    stop_publication: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        if self.stop_publication && event.phase == ExecutionPhase::Publication {
            return Err("publication");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(971))
}

fn provenance(languages: &[NativeSourceLanguage]) -> NativeBundleProvenance {
    NativeBundleProvenance {
        source_languages: languages.iter().copied().collect(),
        ..NativeBundleProvenance::default()
    }
}

fn module(producers: &[Option<Producer>]) -> Module {
    let mut module = Module::new("coverage-fixture");
    for (index, producer) in producers.iter().enumerate() {
        let mut function = Function::new(
            FuncId::new(index as u32),
            "f",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        function.producer = producer.clone();
        module.functions.push(function);
        let mut import =
            ModuleImport::new(format!("dependency-{index}"), ProofDigest::sha256([3; 32]));
        import.producer = producer.clone();
        module.imports.push(import);
    }
    module
}

fn all_producers() -> Vec<Option<Producer>> {
    vec![
        None,
        Some(Producer::TRust),
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("other-λ".into())),
    ]
}

fn long_module() -> Module {
    let text = "aλ🦀".repeat(850);
    let mut other = text.clone();
    other.push('!');
    module(&[
        Some(Producer::Other(text.clone())),
        Some(Producer::TRust),
        Some(Producer::Other(text)),
        Some(Producer::Other(other)),
        None,
    ])
}

fn functions(provenance: &NativeBundleProvenance, module: &Module) -> FunctionRows {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let rows = provenance
        .uncovered_functions_observed(module, &mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    rows
}

fn imports(provenance: &NativeBundleProvenance, module: &Module) -> ImportRows {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let rows = provenance
        .uncovered_imports_observed(module, &mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    rows
}
