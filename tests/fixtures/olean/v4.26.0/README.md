# .olean Test Fixtures (Lean 4.26.0)

This fixture set exists to prove that `clean-olean` still parses and loads a
real Lean 4.26.0 `.olean`, after Lean's string runtime changes landed in 4.25
and the 4.26 compatibility issue (#190) was opened.

## Directory Structure

```text
v4.26.0/
`-- custom/
    `-- StringCompat.lean/.olean
```

## Regenerating Fixtures

```bash
cd tests/fixtures/olean/v4.26.0/custom
elan run leanprover/lean4:v4.26.0 lean StringCompat.lean -o StringCompat.olean
```

Toolchain used for the checked-in fixture:

- Lean `v4.26.0`
- Commit `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`

## Coverage

`StringCompat.lean` intentionally includes a Unicode `String` literal so the
fixture exercises 4.26-era string objects in the serialized `.olean` payload,
not just the header format.

The checked-in `StringCompat.olean` also confirms that Lean 4.26.0 already uses
the v2 `.olean` header layout.
