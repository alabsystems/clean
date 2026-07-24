# Lean 4.26 Dependency Graph Fixtures

This directory contains a minimal two-module Lean 4.26.0 `.olean` graph for
offline import tests:

```text
Graph.Base  -- no imports; declares Graph.Base.token
Graph.User  -- imports Graph.Base; declares Graph.User.usesBase
```

Both source files use `prelude` so `Graph.Base` has no implicit `Init.Prelude`
dependency. This keeps `load_module_with_deps` coverage focused on checked-in
fixture bytes rather than an installed Lean toolchain or stdlib.

Regenerate from this directory with Lean 4.26.0:

```bash
elan run leanprover/lean4:v4.26.0 lean Graph/Base.lean -o Graph/Base.olean
LEAN_PATH=. elan run leanprover/lean4:v4.26.0 lean Graph/User.lean -o Graph/User.olean
```

The checked-in files were generated with Lean `v4.26.0`, commit
`d8204c9fd894f91bbb2cdfec5912ec8196fd8562`.
