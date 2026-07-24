# Clean TLA+ Specifications

TLA+ formal specifications of Clean's state machines for model checking and verification.

## Files

| File | Component | Properties |
|------|-----------|------------|
| `elaboration.tla` | Elaboration pipeline | Phase ordering, error handling, environment monotonicity |
| `tactics.tla` | Tactic execution (AND-OR search) | Soundness, depth bounds, AND-OR consistency |
| `server.tla` | JSON-RPC server protocol | Concurrency limits, request-response correspondence |

## Running Model Checks

### With TLC (Toolbox)

1. Install TLA+ Toolbox from https://lamport.azurewebsites.net/tla/toolbox.html
2. Create a new spec and import the `.tla` file
3. Create a model with appropriate constants
4. Run TLC model checker

### With ty (Rust)

```bash
# From Clean root
cd ../ty
cargo run -p tla-cli -- check ../clean/specs/elaboration.tla
```

## Model Configuration

Each spec has constants that control model size:

### elaboration.tla
```tla
CONSTANTS
    Decls = {d1, d2, d3}    \* 3 test declarations
    MaxErrors = 2            \* Abort after 2 errors
```

### tactics.tla
```tla
CONSTANTS
    GoalIds = {1, 2, 3}     \* Small goal space
    RappIds = {1, 2, 3}     \* Rule applications
    MetaIds = {1, 2, 3}     \* Metavariables
    Rules = {r1, r2}        \* Available tactics
    MaxDepth = 3             \* Search depth limit
    MaxIterations = 10       \* Iteration limit
```

### server.tla
```tla
CONSTANTS
    ClientIds = {c1, c2}        \* Two clients
    RequestIds = {r1, r2, r3}   \* Request IDs
    StateIds = {s1, s2}         \* Proof state cache IDs
    Methods = {method1, method2} \* RPC methods
    MaxConcurrent = 2            \* Connection limit
    MaxPendingRequests = 3       \* Per-connection limit
```

## Verified Properties

### Safety (checked as invariants)

- **TypeOK**: All variables have expected types
- **Phase ordering**: No phase skipping in elaboration pipeline
- **Environment monotonicity**: Declarations never removed
- **Soundness**: Proven proofs are valid
- **AND-OR consistency**: Search tree semantics respected
- **Concurrency limits**: Connection count bounded

### Liveness (checked with fairness)

- **Progress**: Processing eventually completes or errors
- **Termination**: Tactic search terminates (success/fail/timeout)
- **Graceful shutdown**: Server shuts down when requested

## Related

- `crates/clean-tla/` - TLA+ encoding for proof obligations and TLAPS benchmark runner
- `alabsystems/ty` - Rust TLA+ tooling
