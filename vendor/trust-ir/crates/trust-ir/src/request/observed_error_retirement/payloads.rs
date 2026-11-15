// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn producer(&mut self, producer: Option<Producer>) {
        self.record(1, size_of::<Option<Producer>>());
        match producer {
            Some(Producer::Other(text)) => self.text(text),
            None
            | Some(
                Producer::TRust
                | Producer::Clean
                | Producer::TrustIr
                | Producer::TSwift
                | Producer::TC,
            ) => self.fixed(()),
        }
        self.poll();
    }
    pub(super) fn formula(&mut self, site: FormulaSite) {
        self.record(1, size_of::<FormulaSite>());
        match site {
            FormulaSite::Obligation(id) => self.fixed(id),
            FormulaSite::SummaryClause {
                function,
                clause,
                index,
            } => self.fixed((function, clause, index)),
            FormulaSite::SpecInvariant { machine, invariant } => {
                self.text(machine);
                self.text(invariant);
            }
            FormulaSite::SpecTemporal { machine, property } => {
                self.text(machine);
                self.text(property);
            }
        }
        self.poll();
    }
    pub(super) fn lineage_rows(&mut self, mut rows: Vec<ProofLineageError>) {
        self.record(1, size_of::<Vec<ProofLineageError>>());
        loop {
            self.record(1, size_of::<Option<ProofLineageError>>());
            let Some(error) = rows.pop() else {
                break;
            };
            self.lineage(error);
        }
        self.record(
            1,
            rows.capacity()
                .saturating_mul(size_of::<ProofLineageError>()),
        );
        drop(rows);
        self.poll();
    }
}
