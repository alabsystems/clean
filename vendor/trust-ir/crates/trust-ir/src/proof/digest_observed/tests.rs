// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            return Err("original digest stop");
        }
        self.work = self
            .work
            .checked_add(progress.work)
            .ok_or("original overflow")?;
        if self.limit.is_some_and(|limit| self.work > limit) {
            return Err("original work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(13))
}

#[test]
fn domain_framing_and_success_match_the_existing_digest_at_every_chunk_boundary() {
    let long_domain = "domain_λ".repeat(1025);
    for domain in [
        "",
        "trust_ir.native.verification.bundle.v8",
        "domain_λ",
        long_domain.as_str(),
    ] {
        for len in [0, 1, 1023, 1024, 1025, 4097] {
            let bytes = (0..len).map(|n| (n % 251) as u8).collect::<Vec<_>>();
            let mut observer = Observer::default();
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let actual = ProofDigest::sha256_domain_observed(domain, &bytes, &mut session, site())
                .expect("original owner accepts");
            assert_eq!(actual, ProofDigest::sha256_domain(domain, &bytes));
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(observer.events.iter().all(|event| event.site == site()));
            assert!(
                observer
                    .events
                    .iter()
                    .skip(1)
                    .all(|event| event.copy_bytes <= CHUNK_BYTES)
            );
        }
    }
}

#[test]
fn initial_interior_and_final_refusal_never_publish_digest_or_resume() {
    let bytes = vec![7; 4097];
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ProofDigest::sha256_domain_observed("domain", &bytes, &mut session, site()).expect("baseline");
    let polls = measured.events.len();
    for stop_at in 1..=polls {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            ProofDigest::sha256_domain_observed("domain", &bytes, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().expect("cause").cause,
            "original digest stop"
        );
        assert!(ProofDigest::sha256_domain_observed("", &[], &mut session, site()).is_err());
        assert_eq!(observer.events.len(), stop_at);
    }
}

#[test]
fn cumulative_hash_work_is_not_renewed_for_a_second_digest() {
    let bytes = vec![9; 2049];
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ProofDigest::sha256_domain_observed("domain", &bytes, &mut session, site()).expect("baseline");
    let cost = measured.work;
    let mut observer = Observer {
        limit: Some(cost),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    ProofDigest::sha256_domain_observed("domain", &bytes, &mut session, site()).expect("first");
    assert!(ProofDigest::sha256_domain_observed("domain", &bytes, &mut session, site()).is_err());
    assert_eq!(
        session.first_refusal().expect("cause").cause,
        "original work"
    );
}
