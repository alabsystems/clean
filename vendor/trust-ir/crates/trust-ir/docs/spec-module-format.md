<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Copyright 2026 Andrew Yates -->

# `SpecModule` — the spec ↔ source cross-reference artifact

**Status:** stable (`SpecModule.enforcement` and
`SpecAnchor.projection_target` added append-only in binary format v27).
**Owner:** `trust-ir::spec` + `trust-ir::spec_proof`. **Enforced by:** `trust-ir-cli spec-link`.

A `SpecModule` is the TrustIr-native lowering of an authored state-machine
model (a TLA+-style `Model`): its abstract variables, named actions, named
invariants, plus the **bidirectional anchors** that bind each action to a
concrete Rust symbol/span, and the **waivers** that explicitly exempt an action
from requiring a source binding.

`SpecModule` objects live in a `Module` under the new `spec_modules` field. They
roundtrip losslessly through all four serialization formats the toolchain
supports — binary (`.tmbc`), text (`.trust_ir`), JSON, and MessagePack —
so the producer (e.g. aterm's `Model::lower_to_ir`) and the consumer
(`trust-ir-cli spec-link`) can exchange them in whatever format is convenient.

This document is the **precise, authoritative schema**. The aterm side emits
conforming artifacts; this is the contract both ends agree on.

---

## 1. Object model

```
Module {
  …                                       // existing fields
  spec_modules: Vec<SpecModule>           // NEW (binary v13); omitted/empty for legacy modules
}

SpecModule {
  name:       String,                     // machine name; == TLA+ MODULE / Model::name
  vars:       Vec<SpecVar>,               // abstract state variables
  actions:    Vec<String>,                // named actions (the binding targets)
  invariants: Vec<SpecInvariant>,         // named invariants
  anchors:    Vec<SpecAnchor>,            // action ↔ Rust symbol bindings
  waivers:    Vec<SpecWaiver>,            // explicit per-action exemptions
  proofs:     Vec<SpecProof>,             // NEW (binary v14); action ↔ proof-harness bindings; omitted/empty for legacy
  origin:     SpecOrigin,                 // Embedded | External(path)
  enforcement: SpecEnforcementMode,       // (v27): DesignOnly | Linked
  temporal:   Vec<SpecTemporal>,          // TRAILING (v46): named temporal properties; empty on older blobs
}

SpecVar       { name: String, ty: String,             // `ty`: opaque under DesignOnly; Bool | Int | BitVec(<w>) | <lo>..<hi> under Linked
                sort: Option<ClauseSort> }            // v46: the wire sort; must agree with `ty` (both modes); None = NOT RECORDED
SpecInvariant { name: String, formula: String,        // `formula`: opaque under DesignOnly; an SMT-LIB2 Bool term under Linked
                typed: Option<ProofFormula> }         // v46: the SAME first-order clause carrier contract clauses use;
                                                      //      bindings name state variables via ClausePlace::SpecVar { index }
SpecTemporal  { name: String, form: TemporalForm }    // v46: name unique within the machine; an obligation's `spec` backref cites it
TemporalForm  = Always(ProofFormula) | Eventually(ProofFormula) | LeadsTo(ProofFormula, ProofFormula)
              | WeakFair { action, relation: Option<ProofFormula> } | StrongFair { action, relation: Option<ProofFormula> }
                                                      // first-order leaves only (no binder, no Pi/lambda); ONLY a fairness
                                                      // form's `relation` may bind the primed ClausePlace::SpecVarNext { index }

SpecAnchor {
  machine:     String,                    // must resolve to a SpecModule.name (Ob.4)
  action:      String,                    // must be in that machine's `actions` (Ob.1)
  rust_symbol: String,                    // opaque Rust path/DefId text (NOT resolved here — Ob.2 is out of scope)
  span:        String,                    // opaque source span, e.g. "src/ring.rs:120:4"
  project:     Option<String>,            // projection-fn path or named frontend scheme; MUST be nonblank on every present owned anchor (L2)
  function:    Option<FuncId>,            // v26: exact module-local action implementation
  projection_target: Option<SpecProjectionTarget>, // TRAILING (v27): typed/versioned projection resolution
}

SpecWaiver {
  machine: String,                        // must resolve (Ob.4)
  action:  String,                        // must exist (Ob.1)
  reason:  String,                        // reviewed justification (not a silent hatch)
}

SpecProof {                               // NEW (binary v14) — the IR analogue of aterm's proof_anchor!
  machine:    String,                     // must resolve (Ob.4)
  action:     String,                     // must exist (Ob.1)
  proof_name: String,                     // Kani: MUST resolve to a HarnessManifest entry (L1)
  kind:       ProofKind,                  // Kani | CleanTheorem { name } (v46)
}

ProofKind = Kani                          // resolved against the harness manifest (L1)
          | CleanTheorem { name: String } // v46: resolved ONLY against the KernelCertifiedTheorems witness
                                          // trust_ir_build::kernel_certified_theorems mints by validating the module

SpecOrigin = Embedded | External(String)  // External carries the source .tla path
SpecEnforcementMode = DesignOnly | Linked
SpecProjectionTarget = Function(FuncId) | TemporalFieldPathsV1 | ExternalUnresolved
```

### Executable identity

Executable identity is composite. `Module.name` identifies the crate/module
artifact, and `SpecAnchor.function` is the authoritative module-local `FuncId`.
Together `(Module.name, FuncId)` identify the exact executable body. A
frontend may therefore keep `Function.name` and `SpecAnchor.rust_symbol` as
crate-local DefPaths (for example `terminal::Grid::erase`) without redundantly
prefixing the crate name. Those strings are diagnostic provenance, not the
link key; when `function` is populated, validation still requires the target
to exist, carry a body, and have a name exactly equal to `rust_symbol` so the
diagnostics cannot drift from the typed target.

Projection identity follows the same rule when
`projection_target = Function(FuncId)`: the function must exist, carry a body,
match `project` exactly, be non-variadic, and have exactly the canonical
`(&Concrete) -> Abstract` shape. `TemporalFieldPathsV1` is the versioned
intrinsic named `trust-ir.temporal-field-paths.v1`. `ExternalUnresolved` makes
the unresolved state explicit, is invalid for an embedded model, and can never
produce a certifying `Linked` report.

### The harness manifest (resolves `SpecProof.proof_name` — L1)

The standalone IR has no compiler/`DefId` view, so it cannot resolve a Rust
symbol on its own. The aterm build emits a tiny **`HarnessManifest`** JSON that
lists every real `#[kani::proof] fn` (name + span); `spec-link` loads it via
`--harness-manifest <path>` and resolves each `SpecProof.proof_name` against it.

```
HarnessManifest { harnesses: Vec<HarnessEntry> }
HarnessEntry    { name: String, span: String }   // `name` is what a proof_name must match; `span` is opaque
```

Harness names are nonblank identities and must be unique. The public
`link_proofs` API validates this itself and returns `HarnessManifestError`
before attempting L1 resolution, so direct callers cannot accidentally accept
an ambiguous manifest.

```json
{
  "harnesses": [
    { "name": "ring_push_refines", "span": "crates/aterm-buffer/src/ring.rs:300:1" },
    { "name": "ring_pop_refines",  "span": "crates/aterm-buffer/src/ring.rs:340:1" }
  ]
}
```

### Field semantics

| Field | Meaning |
|---|---|
| `SpecModule.name` | The unique, nonblank machine name. Anchors/waivers/proofs reference a `SpecModule` by this string. Matches the TLA+ `MODULE` name / `Model::name`. |
| `vars` | Abstract state variables. Under `DesignOnly`, `ty` is an **opaque** textual tag. Under `Linked` it must be `Bool`, `Int`, `BitVec(<w>)` or `<lo>..<hi>` (an `Int` range), and the name an unprimed SMT simple symbol that is not a surface operator (S3). |
| `actions` | The named transitions of the machine. **Order is preserved.** These are the targets an anchor or waiver may bind to. |
| `invariants` | Named safety properties. Under `DesignOnly`, `formula` is **opaque** surface syntax (TLA+/DSL). Under `Linked` it must be one quantifier-free SMT-LIB2 `Bool` term over the declared, unprimed variables, well-sorted (S3); TLA+ surface syntax is refused there. |
| `anchors` | Each binds one `action` of one `machine` to a concrete source symbol. `function: Some(FuncId)` binds the in-module action implementation. `projection_target` binds either an in-module projection function, the versioned temporal field-path intrinsic, or the explicit external-unresolved state. `rust_symbol`/`span` and `project` remain diagnostic provenance and must agree with typed targets. Every present owned anchor carries a **nonblank projection name** (L2). |
| `waivers` | Each exempts one `action` from requiring an anchor, **with a nonblank reason**. A waiver can cover an absent anchor for Ob.3; it cannot make a malformed present anchor satisfy L2. |
| `proofs` | Each binds one `action` to a named proof harness (`proof_name`) of a given `kind`. The IR analogue of aterm's `proof_anchor!`. A `Kani` `proof_name` is resolved against the supplied `HarnessManifest` (L1); a `CleanTheorem { name }` (v46) is resolved ONLY against the `KernelCertifiedTheorems` witness — never against the module's own `Certified` rows, which the linker cannot re-check (S4). Like an anchor, the `machine`/`action` must satisfy Ob.4/Ob.1. |
| `temporal` | (v46) Named temporal properties: `Always`/`Eventually`/`LeadsTo` over single-state first-order leaves, `WeakFair`/`StrongFair` naming a declared action (Ob.1) with an optional two-state action relation. Every leaf's `bindings` must name THIS machine's variables (`SpecVar`/`SpecVarNext { index }`, index in range, sort agreeing with `SpecVar.sort`), and `SpecVarNext` is legal only in an action relation (S4). A `Liveness`/`TemporalSafety` obligation names the property it discharges through `ProofObligation.spec`. |
| `origin` | `Embedded` for in-source `ty_model!` literals; `External("path/To.tla")` for hand-written TLA parsed via `TlaSpec::parse`. Both bind to source identically. |
| `enforcement` | `DesignOnly` is explicitly non-certifying and makes no total-coverage claim. `Linked` enforces coverage for every action, including when the machine has zero anchors. Current emitters and writers state the mode explicitly; legacy v23–v26 binary and old serde/text inputs map conservatively to `DesignOnly`. |

`Module.name`, machine/member names, reference machine/action fields,
`SpecVar.ty`, `SpecInvariant.formula`, external-origin paths, anchor symbols,
waiver reasons, and proof names must be nonblank. Action, variable, and
invariant names are unique within a machine. A binding is owned by its
containing `SpecModule`, so its redundant `machine` field must equal the
container name; it cannot reach into a sibling machine even when both declare
an action with the same name. Exact duplicate anchor/waiver/proof identities
and an action that is both anchored and waived are structural errors.

> **Out of scope for the standalone CLI:** resolving opaque `rust_symbol` text
> to a live compiler `DefId`. A populated `function` needs no string lookup: it
> is an exact module-local `FuncId`. An external action may retain `None`, but
> its projection resolution must still be explicit in `Linked` mode.

---

## 2. Text format (`.trust_ir`)

A `SpecModule` is rendered as a `spec_module` block, appended to the module
after functions/obligations/certificates. **Every free-form string is quoted**
(Rust `{:?}` escaping: `"` → `\"`, `\` → `\\`, newline → `\n`, tab → `\t`).

### Grammar

```
spec_module "<name>" {
  origin (embedded | external "<path>")     # exactly one origin line, required
  enforcement (design-only | linked)        # current writers emit exactly one mode
  var "<name>" : "<ty>" [sort <sort>]     # zero or more, in order (sort: v46, WS4.4 text)
  action "<name>"                          # zero or more, in order
  invariant "<name>" : "<formula>" [typed <formula-clause>]   # zero or more (typed: v46, WS4.4 text)
  anchor machine "<m>" action "<a>" [function <id>] rust "<sym>" span "<s>" [project "<p>"] [target (none | function <id> | temporal-field-paths-v1 | external-unresolved)]
  waiver machine "<m>" action "<a>" reason "<why>"
  proof  machine "<m>" action "<a>" name "<harness>" kind "<kind>" [theorem "<name>"]   # zero or more (binary v14+; theorem only with kind "clean-theorem", v46)
  temporal "<name>" (always <formula-clause> | eventually <formula-clause>
                     | leads_to <formula-clause> <formula-clause>
                     | weak_fair "<action>" [<formula-clause>]
                     | strong_fair "<action>" [<formula-clause>])   # zero or more, v46 (WS4.4 text)
}
```

`<formula-clause>` and `<sort>` are the shared WS4.4 proof-surface spellings
(`docs/formats.md`): `formula "<schema>" "<payload>" [smtlib ".."] [sort ".."]
[bind "<name>" <sort> <place>]*`, with a spec variable bound as
`spec_var(N)` and its successor value as `spec_var_next(N)`.

Rules:

* The `origin` line is **required**. Current writers also always emit one
  `enforcement` line. A legacy text block without that line is read only
  through the explicit `DesignOnly` compatibility mapping.
* `project` and `target` are optional **at the text-syntax level** for legacy
  decoding. Current writers always emit a `target`, using `target none` for the
  conservative compatibility state. L2 rejects a present owned anchor with no
  nonblank `project`. Every `Linked` anchor rejects a missing typed projection
  target or action `function`, regardless of origin.
* `function` is optional only for design-only/legacy unresolved anchors. It is
  an unsigned module-local `FuncId` and precedes `rust` in canonical text.
* On a `proof` line, `kind` is `"kani"` or, since v46, `"clean-theorem"`
  followed by `theorem "<kernel name>"`.
* The v46 typed carrier (`SpecVar.sort`, `SpecInvariant.typed`, `temporal`)
  is carried by text since WS4.4, in the shared sort / formula spelling above,
  and round-trips exactly. The one residue is a `ClauseSort` nested deeper
  than 64 levels (the reader's cap): a machine carrying one prints the module
  `#lossy` with `spec-carrier(spec_module N)` and the parser refuses the
  marked text. Binary, JSON and MessagePack carry all of it.
* `fmt → parse → fmt` is a byte-for-byte fixed point (the diff-stability
  guarantee asserted by `tests/spec_module_roundtrip.rs`).

### Worked example

```
; TrustIr text format v1
module "spec_pass"

spec_module "ring" {
  origin embedded
  enforcement linked
  var "seq" : "0..7"
  action "Push"
  action "Pop"
  invariant "BoundedSeq" : "(<= seq 7)"
  anchor machine "ring" action "Push" function 0 rust "aterm_buffer::Ring::push" span "crates/aterm-buffer/src/ring.rs:120:4" project "aterm_buffer::Ring::project" target function 1
  waiver machine "ring" action "Pop" reason "pop has no shipping handler yet"
  proof machine "ring" action "Push" name "ring_push_refines" kind "kani"
}
```

An external-origin machine (the ISOLATION-family pattern — pure design intent,
no anchors yet) looks like:

```
spec_module "sandbox" {
  origin external "crates/aterm-spec-models/specs/Sandbox.tla"
  enforcement design-only
  var "entered" : "Bool"
  action "Enter"
  action "Exit"
  invariant "Confined" : "entered => path_confined"
}
```

---

## 3. JSON format

Standard serde representation. Empty `Vec` fields on `SpecModule` are written
out (no `skip_serializing_if`) so the layout is stable across producers; the
top-level `Module.spec_modules` field *is* omitted when empty. `SpecOrigin` is
an externally-tagged enum.

### Worked example

```json
{
  "name": "spec_pass",
  "functions": [],
  "structs": [],
  "enums": [],
  "globals": [],
  "func_types": [],
  "types": [],
  "proof_obligations": [],
  "proof_certificates": [],
  "target_info": null,
  "spec_modules": [
    {
      "name": "ring",
      "vars": [
        { "name": "seq", "ty": "0..7" }
      ],
      "actions": ["Push", "Pop"],
      "invariants": [
        { "name": "BoundedSeq", "formula": "(<= seq 7)" }
      ],
      "anchors": [
        {
          "machine": "ring",
          "action": "Push",
          "rust_symbol": "aterm_buffer::Ring::push",
          "span": "crates/aterm-buffer/src/ring.rs:120:4",
          "project": "aterm_buffer::Ring::project",
          "function": 0,
          "projection_target": { "Function": 1 }
        }
      ],
      "waivers": [
        {
          "machine": "ring",
          "action": "Pop",
          "reason": "pop has no shipping handler yet"
        }
      ],
      "proofs": [
        {
          "machine": "ring",
          "action": "Push",
          "proof_name": "ring_push_refines",
          "kind": "Kani"
        }
      ],
      "origin": "Embedded",
      "enforcement": "Linked"
    }
  ]
}
```

An external origin serializes as `{ "External": "path/To.tla" }`; an anchor
without a projection serializes `"project": null` and
`"projection_target": null`; unit projection targets serialize as
`"TemporalFieldPathsV1"` or `"ExternalUnresolved"`; `ProofKind::Kani`
serializes as the externally-tagged string `"Kani"` and the v46
`CleanTheorem` as `{ "CleanTheorem": { "name": "…" } }`. The v46 fields
serialize as `"sort": null | {…}`, `"typed": null | {…}` and `"temporal": [...]`
(appended after `enforcement`; every one `#[serde(default)]`).

> **MessagePack and binary compatibility note:** the CLI uses the compact (positional) `rmp_serde`
> encoding, which decodes structs as fixed-length sequences. For that reason the
> inner `SpecModule` fields (including the v14 `proofs`) deliberately do **not**
> use `skip_serializing_if` — every field is always present positionally. (The
> JSON above shows the logical shape; MessagePack carries the same fields in
> declaration order.) `SpecAnchor.function` (v26) and
> `SpecAnchor.projection_target` (v27) are append-only serde fields: legacy
> five- and six-field MessagePack anchors decode their missing suffixes to
> `None`. `SpecModule.enforcement` is the final v27 serde field; legacy records
> decode through the named compatibility mapping to `DesignOnly`, never
> implicitly to `Linked`. The binary reader makes the same explicit mappings
> for v23–v26. Current binary/text/serde writers always emit the new fields.

---

## 4. The `spec-link` obligations

```
trust-ir spec-link <module> [--harness-manifest <m>]
                   [--require-manifest | --allow-unverified-proofs]
```

`trust-ir-cli spec-link <module>` loads the module and calls the single public
`trust_ir::link_spec_modules_with_theorems(&module, manifest, theorems,
options)` boundary (`link_spec_modules` is the same call with no witness).
That API performs structural closure, module-local executable resolution,
enforcement policy, coverage, manifest-backed proof resolution and, since v46,
witness-backed Clean-theorem resolution together; the CLI mints the witness
with `trust_ir_build::kernel_certified_theorems` (a full module validation,
in-process CleanCic re-check included) whenever a `clean-theorem` binding is
present, and an invalid module mints none. It prints a
per-machine coverage report and exits 0 only for a certifying report. Any
violation or explicit non-certification reason exits 1. Running `spec-link` on
a module with no `SpecModule` objects is also a usage error (exit 1).

| Obligation | Rule | Catches |
|---|---|---|
| **S0 — unambiguous identity** | Semantic names and payloads are nonblank; machine/member/binding identities are unique; an action cannot be both anchored and waived. | Last-definition-wins machines, duplicate declarations, ambiguous proof/waiver bindings, and metadata that serializes but has no semantic identity. |
| **S1 — container owns binding** | Every anchor, waiver, and proof must name the `SpecModule` that contains it. | A binding stored under machine A silently covering the same-named action of machine B. |
| **S2 — typed resolution** | Every `Linked` anchor has an action `FuncId` and a typed/versioned projection target, regardless of origin. Populated function targets must exist, carry bodies, and agree with their diagnostic names. A function projection must have the exact non-variadic `(&T) -> R` shape. The temporal intrinsic must use its canonical versioned name; `ExternalUnresolved` is forbidden for embedded models. | Stale IDs, declaration-only links, origin-based identity downgrades, label drift, mutable/value projection inputs, and artifacts that claim linkage without a resolvable semantic target. |
| **S3 — linked surface** | For every `Linked` machine: each variable type is `Bool`, `Int`, `BitVec(<w>)` or `<lo>..<hi>` and each variable name an unprimed SMT simple symbol that is not a surface operator (`LinkedVariableUnparsed`); each invariant is one quantifier-free SMT-LIB2 term of sort `Bool` whose free symbols are declared variables (a primed `x'` is allowed only in actions) and whose applications are well-sorted over the core, integer and bit-vector operators, in printable ASCII with only SMT-LIB2 whitespace and at most 256 levels of nesting (`LinkedFormulaUnparsed`). A variable name may not be any function symbol of the `Core`/`Ints`/`FixedSizeBitVectors` theories. (v46) Each typed carrier — a typed invariant or a temporal leaf — that carries an `smtlib` rendering must read as the same kind of term over its OWN `bindings`, which are its whole variable environment (a free symbol they do not bind is undeclared even when the machine declares a variable of that name; a bound name must be an unprimed simple symbol and bound once) — `LinkedTypedCarrierUnparsed`; a carrier with no `smtlib` is not read here, its bindings still being held to S4. A typed invariant's rendering and its string `formula` are ONE predicate: read with each bound name replaced by the state variable its `SpecVar` place indexes, the carrier must be the same s-expression as `formula` (whitespace aside) — `LinkedTypedCarrierDisagrees`, reported only when both renderings read and every binding resolves, so a garbage twin is named once by its own rule. `DesignOnly` strings stay opaque. The module validator reports the same rule as `SpecLinkedVariableUnparsed` / `SpecLinkedFormulaUnparsed` (the typed-carrier rule through `InvalidSpecStructure`). | A certifying link over an invariant nobody can read: garbage syntax, TLA+ surface syntax, an undeclared variable, an ill-sorted comparison, or a variable whose type is not a type — in the string `formula` or, one layer up, in the typed carrier's rendering beside a well-formed binding list. |
| **S4 — typed carrier** | (v46) In BOTH modes: a declared `SpecVar.sort` agrees with its parsed `ty` (`SpecVariableSortMismatch`); every typed invariant / temporal leaf binding names one of this machine's variables by `SpecVar`/`SpecVarNext { index }` in range, at the variable's sort — its declared `sort`, else the sort its `ty` tag parses to (`SpecVar::effective_sort`; an unrecorded `sort` is not a wildcard) — primed only inside a fairness action relation (`SpecTypedBindingInvalid`); a fairness form's `action` is declared (Ob.1); temporal names are unique (S0). A `CleanTheorem` proof binding resolves only against the supplied `KernelCertifiedTheorems` witness (`CleanTheoremUnresolved`); with no witness a `Linked` machine is refused unless the exploratory option is set, which makes the report non-certifying (`clean-theorem-unverified`) — the L1 manifest policy's twin. | A typed clause about a variable the machine does not declare, a primed variable in an invariant, a sort strip that turns a false claim into a true one, and a spec binding that asserts a kernel theorem nothing re-checked. |
| **Ob.1 — action exists** | Every `anchor.action` / `waiver.action` / `proof.action` is in its machine's `actions`. | `#[refines(action="SetOriginMode")]` against a machine with no such action; an external (Next-only) module's anchor naming a non-Next def like `TypeOK` (**L3** — locked by test). |
| **Ob.3 — coverage** | For every `Linked` machine, every action is covered by ≥1 owned anchor **or** a waiver. This remains a hard gate when the machine has zero anchors. `DesignOnly` explicitly makes no coverage claim. | A model action with no shipping handler and no waiver; deleting the last anchor can no longer silently disable coverage. |
| **Ob.4 — machine resolves** | Every `anchor.machine` / `waiver.machine` / `proof.machine` names a `SpecModule` present in the input. | The dead-`TerminalModes.tla` situation — an annotation pointing at nothing. |
| **L1 — proof resolves** | A supplied manifest must have unique, nonblank harness names, and every `proof.proof_name` must resolve to one entry. | A typo'd/dead `proof_anchor!` or an ambiguous generated harness manifest. |
| **L2 — projection present** | Every present owned anchor has a nonblank `project` name (`None`, empty, and whitespace-only fail), even when the action is waived or the module is `DesignOnly`. | An inert projection and attempts to use a waiver or enforcement mode to legitimize malformed metadata. |

**Manifest policy (L1):** proof bindings in a `Linked` machine require a
manifest by default. Missing one is a hard `ProofManifestRequired` violation.
`--allow-unverified-proofs` is the only exploratory override: it suppresses
that one violation but the report remains machine-readably non-certifying
(`code=proof-manifest-unverified`) and the CLI still exits 1. Design-only proof
bindings do not require a manifest unless `--require-manifest` is requested.

**Ob.2 (live Rust `DefId` resolution)** remains out of scope for an
untyped/external anchor: `rust_symbol` alone is opaque. When a frontend provides
`function`, however, `spec-link` enforces the in-module executable target and
its diagnostic-name agreement as described above. Pure design intent must be
declared with `DesignOnly`; it is never inferred from anchor count. A `Linked`
external anchor may explicitly use `ExternalUnresolved`, but that state always
adds `code=external-projection-unresolved`, remains non-certifying, and exits 1.

### Example reports

Passing (with a resolved proof):

```
spec-link: 1 machine(s) in pass.trust_ir
  machine "ring" [embedded] coverage 2/2 = 100.0% (1 anchored, 1 waived) [linked]
spec-link: harness manifest m.json (1 harness), resolved 1 proof binding
spec-link-status: certifying
ok: pass.trust_ir — all spec↔source obligations hold (S0/S1/S2/S3, Ob.1/Ob.3/Ob.4, L2) plus all proof bindings resolved (L1)
```

Failing (Ob.4):

```
spec-link-status: non-certifying
spec-link failed: fail_ob4.trust_ir (1 violation)
  [0] [Ob.4 machine-resolves] anchor for action "SetOriginMode" names machine "terminal_modes" which has no SpecModule in the input (rust_symbol="aterm_terminal::set_origin_mode")
```

Failing (L1 — proof_name unresolved):

```
spec-link-status: non-certifying
spec-link failed: fail_l1.trust_ir (1 violation)
  [0] [L1 proof-resolves] machine "ring": proof for action "Push" names harness "does_not_exist" which is not in the supplied harness manifest
```

Failing (L2 — missing projection):

```
spec-link-status: non-certifying
spec-link failed: fail_l2.trust_ir (1 violation)
  [0] [L2 projection-present] machine "ring": anchor for action "Pop" carries no projection name (project is absent or blank) — fill a real projection fn path, or remove the anchor and use a waiver
```

Violation-free but non-certifying (explicit unresolved external projection):

```
spec-link-status: non-certifying
spec-link-noncert: code=external-projection-unresolved detail="machine \"ring\" action \"Push\" uses an external-unresolved projection"
```
