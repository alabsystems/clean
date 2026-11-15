// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A Lean-built module's own `@[implemented_by]` bindings, judged against what
//! pinned Lean compiled before them (`docs/DECISIONS.md` R149).
//!
//! An imported binding is registered so that every compiled reference to the
//! declaration runs its implementation, which is what Lean's compiled code
//! does only when Lean never compiled code from the declaration's own body.
//! Lean compiles a declaration when it is added; a binding written ON the
//! declaration is applied before that, so the declaration is never compiled
//! (no IR), and every caller substitutes the implementation. A binding written
//! LATER (`attribute [implemented_by t] d`) finds `d` already compiled, and
//! then, measured with `lean --run` (pinned v4.30.0-rc2, `t n := Nat.add n 1`,
//! `d n := Nat.add n 2`):
//!
//! * code of the module added before the command keeps running `d`'s body
//!   (`caller n := Nat.mul (d n) 10` prints `30` for `caller 1`; with the
//!   binding it would be `20`), through a call or an inlined copy;
//! * an inline candidate's pre-binding body is copied into callers compiled
//!   after the command, in the module and in every importer: `@[inline] d`
//!   prints `3` for an importer's `d 1`, and so does `def d (n : Nat) : Nat :=
//!   n` (LCNF size at most `compiler.small`) under `t n := Nat.add n 100`;
//!   only `@[noinline] d` prints the implementation's answer there;
//! * a structure projection is compiled structurally, so `attribute
//!   [implemented_by pf] P.a` never runs `pf` (an importer's `P.a ⟨1⟩` prints
//!   `1`), and the projection has no IR.
//!
//! `@[macro_inline]` is the other exception: its body is expanded at every
//! call site, on-declaration binding or not, so the loader does not register
//! the binding at all ([`CompilerNames::macro_inline`]).
//!
//! So a binding of a declaration that has IR is LATE unless the IR shows it
//! was compiled after its binding (a recursive declaration bound on itself is
//! compiled, and its recursive calls run the implementation:
//! [`compiled_after_binding`]). A late binding records, in the environment's
//! order record (`Environment::record_compiled_before`), the module's own
//! constants that reach the declaration, and the declaration itself unless it
//! is `@[noinline]`; every compiled lane then refuses every root, as it does
//! for the same command in a file it elaborates. A binding of a declaration
//! without IR is on-declaration unless the declaration is one Lean compiles
//! structurally ([`compiled_structurally`]) and the binding is not one of a
//! computed field ([`computed_field_override`]); such a late one is recorded
//! too. Anything this cannot read (a table, the IR files of a `module`,
//! another Lean version's IR bodies) is taken as late.

use std::collections::{HashMap, HashSet};

use clean_kernel::env::{CompiledBefore, Environment};
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::ConstantKind;

use super::load_parse::LoadModule;
use super::load_shadowing::foreign_resident_provenance;
use crate::lean_ir::module_ir::ModuleIr;
use crate::lean_ir::types::{Alt, Decl, Expr as IrExpr, FnBody, Instr, Terminal};
use crate::module::typed_extensions::TypedExtension;

#[path = "late_binding_ir.rs"]
mod ir;
use ir::IrSource;

/// `Lean.IR.declMapExt`'s persisted name.
const DECL_MAP_EXT: &str = "Lean.IR.declMapExt";
/// `Lean.Compiler.inlineAttrs`'s persisted name.
const INLINE_ATTRS_EXT: &str = "Lean.Compiler.inlineAttrs";
/// `InlineAttributeKind.noinline`.
const NOINLINE: u64 = 1;
/// `InlineAttributeKind.macroInline`.
const MACRO_INLINE: u64 = 2;
/// `InlineAttributeKind.inlineIfReduce`.
const INLINE_IF_REDUCE: u64 = 3;

/// The names a part's compiler tables give, read beside its rows
/// (`TypedExtension::compiler_names`): `None` when a table did not read.
pub(super) struct CompilerNames {
    /// Declarations with IR in the part's `Lean.IR.declMapExt`. For a
    /// `module`-system file this is not every compiled declaration (private
    /// IR is only in the `.ir` file), so it is not read for one.
    ir: Option<HashSet<Name>>,
    /// Each declaration's `Lean.Compiler.inlineAttrs` kind.
    inline: Option<HashMap<Name, u64>>,
}

impl CompilerNames {
    /// The names `extensions` (one part's tables) carry. A table the part
    /// does not hold has no rows: pinned Lean writes no table for an
    /// extension with nothing to export (`computeExtEntries`'s
    /// `filterNonEmpty`, `Lean/Environment.lean`), so a module without one
    /// inline attribute has no `inlineAttrs` table. Judging that as unread
    /// refused every root of `ImplByLib`, whose bindings are all on their
    /// declarations. That is the only reason a table is absent from the part
    /// the loader reads tables from, which holds every level's entries: a
    /// non-`module` file's `.olean` is written at the private level
    /// (`writeModule`), and a `module`'s tables are read from its
    /// `.olean.private` (`load_register`'s `PartEntries::Read`); Lean v4.8.0
    /// writes every table. A table the part holds but whose rows did not read
    /// is unknown.
    pub(super) fn of(extensions: &[TypedExtension]) -> Self {
        let table = |dotted: &str| -> Option<&[(Name, u64)]> {
            let name = Name::interned(dotted);
            match extensions
                .iter()
                .find(|extension| extension.extension_name == name)
            {
                None => Some(&[]),
                Some(extension) => extension.compiler_names.as_deref(),
            }
        };
        Self {
            ir: table(DECL_MAP_EXT).map(|rows| rows.iter().map(|(name, _)| name.clone()).collect()),
            inline: table(INLINE_ATTRS_EXT).map(|rows| rows.iter().cloned().collect()),
        }
    }

    /// No table read: every judgement is "unknown".
    pub(super) fn unknown() -> Self {
        Self {
            ir: None,
            inline: None,
        }
    }

    /// Whether `decl` is `@[macro_inline]`, `None` when the table did not
    /// read. Pinned Lean expands such a declaration's body at every call site
    /// before an `@[implemented_by]` substitution could apply, whether the
    /// binding is on the declaration or later: `@[macro_inline,
    /// implemented_by fast] def slow (n : Nat) : Nat := Nat.add n 2` prints
    /// `3` for an importer's `slow 1` (`fast` gives `2`), and Lean v4.8.0
    /// prints the same. The loader registers no such binding.
    pub(super) fn macro_inline(&self, decl: &Name) -> Option<bool> {
        self.inline
            .as_ref()
            .map(|kinds| kinds.get(decl) == Some(&MACRO_INLINE))
    }
}

/// Record, for each binding `(declaration, target)` that `module`'s part
/// `part` registered for its own declaration, what pinned Lean compiled from
/// the declaration's body before the binding (module docs). A `.olean` does
/// not say which of its constants were added before the command, so a late
/// binding records EVERY own constant that reaches the declaration: more
/// than Lean ran the old body for, which changes only the names a refusal
/// prints, since every root is refused either way.
pub(super) fn record_late_bindings(
    env: &mut Environment,
    module: Option<&str>,
    part: &LoadModule,
    names: &CompilerNames,
    bindings: &[(Name, Name)],
) {
    if bindings.is_empty() {
        return;
    }
    let own: HashSet<Name> = part
        .constants
        .iter()
        .map(|constant| &constant.kernel_name)
        .filter(|name| {
            env.get_const(name).is_some()
                && foreign_resident_provenance(env, name, module, false).is_none()
        })
        .cloned()
        .collect();
    let mut ir = IrSource::new(
        module,
        part.source_olean.as_deref(),
        part.captured_ir.clone(),
    );
    let mut found = Vec::new();
    for (decl, target) in bindings {
        if let Some(own_code) = late(env, &own, names, &mut ir, part.is_module, decl, target) {
            found.extend(env.compiled_before_binding(&HashSet::from([decl.clone()]), Some(&own)));
            // A `module`'s constants are split across its parts, so the scan
            // of this part may miss a referrer in another: the declaration
            // itself is recorded whatever its inline attribute.
            if own_code || part.is_module {
                found.push((
                    decl.clone(),
                    CompiledBefore {
                        rebound: decl.clone(),
                        via: decl.clone(),
                    },
                ));
            }
        }
    }
    if !found.is_empty() {
        tracing::debug!(
            module = module.unwrap_or("?"),
            recorded = found.len(),
            "imported `@[implemented_by]` binding came after compiled code"
        );
        env.record_compiled_before(found);
    }
}

/// `Some(own_code)` when the binding of `decl` to `target` is late (module
/// docs), with whether `decl`'s own compiled code can be copied into callers
/// compiled after it; `None` when Lean compiled nothing from `decl`'s body
/// before the binding.
fn late(
    env: &Environment,
    own: &HashSet<Name>,
    names: &CompilerNames,
    ir: &mut IrSource,
    is_module: bool,
    decl: &Name,
    target: &Name,
) -> Option<bool> {
    let Some(kind) = names.inline.as_ref().map(|kinds| kinds.get(decl).copied()) else {
        return Some(true);
    };
    let has_ir = if is_module {
        ir.names().map(|compiled| compiled.contains(decl))
    } else {
        match &names.ir {
            Some(compiled) => Some(compiled.contains(decl)),
            None => ir.names().map(|compiled| compiled.contains(decl)),
        }
    };
    let Some(has_ir) = has_ir else {
        return Some(true);
    };
    if !has_ir {
        return (compiled_structurally(env, decl) && !computed_field_override(env, decl, target))
            .then_some(true);
    }
    if kind != Some(INLINE_IF_REDUCE)
        && ir
            .bodies()
            .is_some_and(|bodies| compiled_after_binding(env, own, bodies, decl, target))
    {
        return None;
    }
    Some(kind != Some(NOINLINE))
}

/// Whether Lean compiles `decl` without a function of its own, so that it
/// has no IR whenever it is bound: a structure projection (compiled as a
/// field access, measured above), one of the auxiliary definitions Lean's
/// `toLCNF` expands where it is used (`casesOn`, matchers, the structural
/// recursion helpers, `noConfusion`), a constructor, a recursor or a type
/// (Clean holds these as definitions without a value, so they are asked
/// for by name), or a theorem. A binding of one is never run by Lean:
/// `attribute [implemented_by pf] P.mk` leaves `(P.mk 1).a` printing `1` in
/// Lean, where `pf` gives `11` (`LateCtor`). Registering it crashed the
/// importer (`clean run` exit 139, a SIGSEGV): `pf`'s own body builds a
/// `P.mk`, which the binding rewrites to `pf`.
///
/// A definition, an opaque and an axiom are called: Lean runs the
/// implementation of an axiom bound on its declaration (`LateAx`'s
/// `axCaller 1` prints `20`), and a `module`'s public part exports a
/// definition or opaque whose body it does not expose as an axiom (pinned
/// `Lean.Attributes`' `@[implemented_by mkAttributeImplOfConstantUnsafe]
/// opaque mkAttributeImplOfConstant`, which no other part of the module
/// holds). Reading an axiom as compiled structurally judged that binding late
/// and refused every program importing `Lean`.
///
/// A name that ends in a number is a hygienic one (`hygSlow._@.M.<hash>.
/// _hygCtx._hyg.3`, the `TypeName` instances pinned `Std` derives): no
/// auxiliary suffix or field name ends that way, so only the kind decides.
/// Reading every such name as compiled structurally judged their on-
/// declaration bindings late and refused every program importing `Std`.
fn compiled_structurally(env: &Environment, decl: &Name) -> bool {
    if env.get_constructor(decl).is_some()
        || env.get_recursor(decl).is_some()
        || env.get_inductive(decl).is_some()
        || env.get_quot(decl).is_some()
    {
        return true;
    }
    let not_a_function = || {
        !env.get_const(decl).is_some_and(|info| {
            matches!(
                info.kind,
                ConstantKind::Definition | ConstantKind::Opaque | ConstantKind::Axiom
            )
        })
    };
    let (parent, last) = match decl.inner() {
        NameInner::Str(parent, last) => (parent, last),
        NameInner::Num(..) => return not_a_function(),
        NameInner::Anon => return true,
    };
    let last: &str = last;
    if env
        .get_structure_field_index(parent, &Name::anon().str(last))
        .is_some()
    {
        return true;
    }
    matches!(
        last,
        "casesOn"
            | "recOn"
            | "brecOn"
            | "binductionOn"
            | "below"
            | "ibelow"
            | "noConfusion"
            | "noConfusionType"
            | "ctorIdx"
            | "toCtorIdx"
            | "_sunfold"
            | "_unsafe_rec"
    ) || last.starts_with("match_")
        || last.starts_with("proof_")
        || not_a_function()
}

/// Whether `decl → target` is a binding pinned Lean's computed-field
/// elaborator writes (`Lean/Elab/ComputedFields.lean`, `setComputedFields`):
/// an inductive's `casesOn` or one of its constructors bound to its own
/// `_override`. The elaborator sets these while it elaborates the inductive,
/// before anything that uses them is compiled, and Lean's compiler honours
/// them at every use (`toMono` lowers such a `casesOn` to the `_impl`
/// representation; the `implementedBy` simp pass substitutes a constructor).
/// So, though Lean compiles both structurally, the binding is not late:
/// pinned `Init.Prelude`'s `Lean.Name.casesOn` → `Lean.Name.casesOn._override`
/// (measured: judging it late recorded 101 constants of `Init`, among them
/// `Lean.Name.beq` and `Lean.Name.instBEq`, and refused every program that
/// imports `Init`). Any other binding of a structurally compiled declaration
/// stays late.
fn computed_field_override(env: &Environment, decl: &Name, target: &Name) -> bool {
    let shape = match decl.inner() {
        NameInner::Str(_, last) => {
            let last: &str = last;
            last == "casesOn" || env.get_constructor(decl).is_some()
        }
        _ => false,
    };
    shape && *target == decl.clone().str("_override")
}

/// Whether `decl`'s IR proves it was compiled AFTER its binding to `target`:
/// its code (its IR declaration and the compiler-generated ones it calls)
/// calls `target` or one of `target`'s compiler artifacts, and nothing but
/// the binding can put `target` there. That is how a recursive declaration
/// bound on itself compiles (Lean compiles it, and its recursive calls are
/// substituted): measured on pinned v4.30's `List.mapMonoM` and
/// `Lean.Expr.replaceLevel`, the only bound declarations with IR in `Init`,
/// `Std` and `Lean`, and on `@[implemented_by recFast] def recSlow` (fixture
/// family `implemented_by_late`, whose IR calls `recFast` where it recurses).
///
/// "Nothing but the binding" is decided over this module's own constants:
/// `target` must be one of them, and no own constant `decl`'s value reaches
/// (through values and other bindings, never `decl`'s own) may be `target`
/// or a constant under `target`'s name, nor may an own theorem's statement
/// name one (a `@[csimp]` lemma could rewrite to it). An imported constant
/// cannot reach an own one, so the walk never leaves the module.
fn compiled_after_binding(
    env: &Environment,
    own: &HashSet<Name>,
    bodies: &ModuleIr,
    decl: &Name,
    target: &Name,
) -> bool {
    if !own.contains(target) {
        return false;
    }
    let targets: Vec<&Name> = own.iter().filter(|name| has_prefix(name, target)).collect();
    let decls: HashMap<&Name, &Decl> = bodies.ir_decls().iter().map(|d| (d.name(), d)).collect();
    let called = ir_callees(env, &decls, decl);
    let calls_target = called.iter().any(|callee| {
        has_prefix(callee, target) && (env.get_const(callee).is_none() || own.contains(callee))
    });
    if !calls_target {
        return false;
    }
    // A `@[csimp]` lemma (or anything stating an equation) about the target.
    let stated = own.iter().any(|name| {
        env.get_const(name).is_some_and(|info| {
            info.kind == ConstantKind::Theorem && {
                let mut used = HashSet::new();
                info.type_
                    .used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
                used.iter().any(|used| targets.contains(&used))
            }
        })
    });
    if stated {
        return false;
    }
    // Own constants reachable from `decl`'s value without its own binding.
    let mut seen: HashSet<&Name> = HashSet::new();
    let mut stack: Vec<Name> = Vec::new();
    let push_value = |name: &Name, stack: &mut Vec<Name>| {
        if let Some(value) = env.get_const(name).and_then(|info| info.value.as_ref()) {
            let mut used = HashSet::new();
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            stack.extend(used.into_iter().filter(|used| own.contains(used)));
        }
    };
    push_value(decl, &mut stack);
    while let Some(name) = stack.pop() {
        let Some(name) = own.get(&name) else {
            continue;
        };
        if !seen.insert(name) {
            continue;
        }
        if targets.contains(&name) {
            return false;
        }
        if name != decl {
            if let Some(next) = env.get_implemented_by(name) {
                stack.push(next.clone());
            }
        }
        push_value(name, &mut stack);
    }
    true
}

/// Every function `root`'s IR calls, through the compiler-generated
/// declarations it calls (`_lam`, `_redArg`, `_at_ … spec`, `_closed`):
/// those are walked into, and a call to a constant of the environment ends
/// the walk there.
fn ir_callees(env: &Environment, decls: &HashMap<&Name, &Decl>, root: &Name) -> HashSet<Name> {
    let mut called: HashSet<Name> = HashSet::new();
    let mut walked: HashSet<&Name> = HashSet::new();
    let mut stack: Vec<&Name> = vec![root];
    while let Some(name) = stack.pop() {
        let Some((&name, decl)) = decls.get_key_value(name) else {
            continue;
        };
        if !walked.insert(name) {
            continue;
        }
        let Decl::FDecl { body, .. } = decl else {
            continue;
        };
        let mut found = Vec::new();
        body_callees(body, &mut found);
        for callee in found {
            if env.get_const(callee).is_none() {
                if let Some((&key, _)) = decls.get_key_value(callee) {
                    stack.push(key);
                }
            }
            called.insert(callee.clone());
        }
    }
    called
}

/// The callees of the `fap` / `pap` expressions of `body`, join points and
/// `case` alternatives included.
fn body_callees<'b>(body: &'b FnBody, out: &mut Vec<&'b Name>) {
    for instr in &body.instrs {
        match instr {
            Instr::VDecl {
                e: IrExpr::Fap { f, .. } | IrExpr::Pap { f, .. },
                ..
            } => out.push(f),
            Instr::JDecl { body, .. } => body_callees(body, out),
            _ => {}
        }
    }
    if let Terminal::Case { alts, .. } = &body.terminal {
        for alt in alts {
            match alt {
                Alt::Ctor { body, .. } | Alt::Default { body } => body_callees(body, out),
            }
        }
    }
}

/// Whether `name` is `prefix` or a name under it (`t._redArg`,
/// `t._at_.f.spec_0`).
fn has_prefix(name: &Name, prefix: &Name) -> bool {
    let mut current = name;
    loop {
        if current == prefix {
            return true;
        }
        match current.inner() {
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
            NameInner::Anon => return false,
        }
    }
}

#[cfg(test)]
#[path = "late_binding_tests.rs"]
mod tests;
