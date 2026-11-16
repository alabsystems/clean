The new `semr_unsigned_translation` modules import unchanged `semr_wp`
prerequisites. The integration test compiles only these added modules with the
pinned Lean binary, then checks their actual dependency closure in the closed
reference kernel.

`unsigned-select-production.json` is a fresh complete SharedIR module submitted
to production native WP7e99. Its 764-byte original module, 387-byte stored typed
contract and 5875-byte emitted VC are retained exactly. The module is decoded by
canonical SemR; it is never replaced by a projected or hand-reified body. The
proposed JSON is ordinary syntax data whose exact encoding and typed decoding
are checked with the existing codecs. All Bool × U64 × U64 signature-valid
inputs and call-depths are covered, including U64::MAX.

`originalWpTranslation` is conditional on the actual VC being true after total
typed evaluation. `original_execution` composes the proved translation with the
actual VC's validity. The generic Select/Return rule uses actual canonical PCs,
eager operand/type checks and the SSA result read by Return. This finite theorem
does not certify every translation emitted by the Rust implementation, change
Trusted/Deductive grades or authenticate source/ABI/emitted machine bytes.

`unsigned-select-layout-unsupported.json` retains the complete earlier 815-byte
packet. Its physical field offsets are deliberately unsupported by canonical
SemR. The Lean control pins that refusal; none of its records were stripped to
create the fresh scalar input. The remaining full-goal gaps are still open.

The production mathematical context checks `TranslationCertificate`, an indexed
Prop whose only field is the unchanged `originalWpTranslation` proof. Its exact
input indices let the kernel reject a different question without expanding the
whole semantic proposition; `certificate_sound` extracts that proposition and
is separately included in the closed replay. The heartbeat budget is unchanged.
