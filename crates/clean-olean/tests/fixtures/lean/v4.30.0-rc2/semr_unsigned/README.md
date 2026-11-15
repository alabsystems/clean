This family uses the one canonical SemR module. `SemRUnsignedSelect` proves
unsigned Gt/not-Le and Ge/not-Lt identities with the necessary exchange of
both choice arms, then relates typed comparison, selection and storage to
canonical instructions. Source-domain bounds remain explicit.

`SemRUnsignedClamp` quotes the complete retained native U32 `clamp_width` and
U64 `clamp_to_max` bodies. Their universal proofs compose individual SemR
steps and the existing load-after-store theorem. The native regression binds
the quotations to complete serialized modules, checks boundary inputs with
the reference interpreter, rechecks one closed theorem dependency set in
Clean's ReferenceKernel, and rejects proof transfers to wrong comparison,
arm and bound variants in that same checked environment.

This family adds no decoder, interpreter, source parser or proof axiom.
Rust/MIR/THIR-to-IR lowering remains a separate trusted translation boundary.
The division family imports only the shared select primitives.
