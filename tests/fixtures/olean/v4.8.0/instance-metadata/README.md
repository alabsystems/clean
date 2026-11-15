# Lean 4.8 class and instance metadata

`InstanceParity.lean` is the existing import-free instance-parity fixture, compiled
verbatim with the genuine Lean 4.8.0 oracle. Its two classes and two instances
contrast with ordinary class-typed definitions and an ordinary structure.

- Source SHA-256: `7d2341be479a0d57ad8fcbdf43e1df164d16ff905c8ff88f81c69f43d9d98b7e`
- Olean SHA-256: `aab5060a80fc6aed276c39c6e5261f3f2187eb5f1c0cfd63a5dad539cb5dfe4f`
- Oracle executable SHA-256: `b64386089a2ba20faf662a867bf6f7ebe724e44f02987568224dada9fc0708fd`
- Command: `lean -o InstanceParity.olean InstanceParity.lean`

Lean v4.8 `Lean/Class.lean` defines `ClassEntry` with `name` and `outParams`;
there is no `outLevelParams` field. Its `Lean/Meta/Instances.lean` defines the
same five object fields plus `attrKind` used by the existing instance reader.
These are metadata reads, not authority for a declaration or a proof.
