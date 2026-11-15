# `semr_forged` — the negative control of the SemR audit (RM4)

One module (`SemRForged.lean`, `ORDER`) the pinned `lean -o` compiles. It puts in SemR's
namespace what SemR must never carry, behind the `'"'` character literal the RM4 review used to
blind the first source tripwire: `SemR.smuggled`, closed by `native_decide` (at v4.30 the proof
cites its own auxiliary axiom `SemR.smuggled._native.native_decide.ax_…`), and `SemR.spin`, a
`partial def` (an opaque constant beside the unsafe `SemR.spin._unsafe_rec`).

`crates/clean-olean/tests/semr_reference.rs` holds both layers to it:
`semr_audit_reports_smuggled_constants` (every declared constant through the reference entry;
`SemR.smuggled` and `SemR.spin` are reported by name, `SemR.dq`, `SemR.honest` and
`SemR.honest_eq` are not) and `semr_tripwire_catches_the_forged_fixture` (the source scan reports
`native_decide` and `partial`).
