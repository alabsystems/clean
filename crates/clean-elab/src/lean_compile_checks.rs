// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The refusals Lean makes outside its kernel that Clean's kernel does not
//! make: what its code generator cannot compile, what `#eval` will not run,
//! and the safe context a safe declaration is checked in.
//!
//! Clean has no code generator in the elaboration loop, so nothing refused
//! `def x : Nat := Classical.choice ⟨0⟩` (Lean: "failed to compile
//! definition, consider marking it as 'noncomputable'"), `#eval` of a term
//! that depends on `sorry`, or a safe declaration that uses an `unsafe`
//! constant (Lean's kernel checks it in a safe context; Clean's extended
//! kernel theory admits it). Review round r6 (X1, X10, X11, docs/DECISIONS.md
//! R134-R135) measured each against pinned Lean 4.8.0 and 4.30.0-rc2.
//!
//! * `#eval` is refused everywhere ([`eval_refusal`]): `clean check` prints
//!   the value, so a value Lean would not compute is wrong output there too.
//! * Source frontends enable `FrontDoorScope`: safe-context refusals happen
//!   before admission; computability errors are attached after registration and
//!   genuine attribute application. Later commands retain the actual value.
//!   Pure logical elaboration may leave this source-compiler policy disabled.

use crate::print_axioms::{collect_axioms_of_all, used_constants_in_order};
use clean_compiler::CompilerError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, LocalContext, TypeChecker};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

thread_local! {
    static FRONT_DOOR: Cell<bool> = const { Cell::new(false) };
    static NONCOMPUTABLE_SECTION: Cell<u32> = const { Cell::new(0) };
    static DEFERRED_MARKS: RefCell<Vec<Name>> = const { RefCell::new(Vec::new()) };
}

/// While alive (and entered with `true`), every declaration this thread
/// registers is held to Lean source-compiler and safe-context checks
/// ([`front_door_active`]). Entered by the source frontend's module driver.
pub(crate) struct FrontDoorScope {
    previous: bool,
}

impl FrontDoorScope {
    pub(crate) fn enter(active: bool) -> Self {
        let previous = FRONT_DOOR.with(|cell| cell.replace(active));
        Self { previous }
    }
}

impl Drop for FrontDoorScope {
    fn drop(&mut self) {
        FRONT_DOOR.with(|cell| cell.set(self.previous));
    }
}

/// Whether this thread is elaborating under source-compiler policy.
pub(crate) fn front_door_active() -> bool {
    FRONT_DOOR.with(Cell::get)
}

/// While alive (and entered with `true`), the declarations this thread
/// elaborates are inside a `noncomputable section`: Lean marks one its
/// compiler cannot compile `noncomputable` instead of refusing it.
pub(crate) struct NoncomputableSectionScope {
    entered: bool,
}

impl NoncomputableSectionScope {
    pub(crate) fn enter(noncomputable: bool) -> Self {
        if noncomputable {
            NONCOMPUTABLE_SECTION.with(|depth| depth.set(depth.get() + 1));
        }
        Self {
            entered: noncomputable,
        }
    }
}

impl Drop for NoncomputableSectionScope {
    fn drop(&mut self) {
        if self.entered {
            NONCOMPUTABLE_SECTION.with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }
}

/// Whether this thread is inside a `noncomputable section`.
pub(crate) fn in_noncomputable_section() -> bool {
    NONCOMPUTABLE_SECTION.with(Cell::get) > 0
}

/// Record that `name`, being elaborated now, is to be marked `noncomputable`
/// when it registers ([`take_deferred_noncomputable_marks`]).
pub(crate) fn defer_noncomputable_mark(name: Name) {
    DEFERRED_MARKS.with(|marks| marks.borrow_mut().push(name));
}

/// The marks [`defer_noncomputable_mark`] recorded, drained.
pub(crate) fn take_deferred_noncomputable_marks() -> Vec<Name> {
    DEFERRED_MARKS.with(|marks| std::mem::take(&mut *marks.borrow_mut()))
}

fn unknown_payload_compiler_context(env: &Environment, name: &Name) -> bool {
    matches!(
        env.get_constant_origin(name),
        Some(clean_kernel::ConstantOrigin::CleanPayload { .. })
    ) && env
        .get_const(name)
        .is_some_and(|info| !matches!(info.kind, clean_kernel::ConstantKind::Axiom))
        && !clean_kernel::env::csimp::has_compilation_context(env, name)
}

/// A runtime reference with no executable implementation. Foreign-code
/// exceptions and source-kind metadata belong to the persistent environment.
fn has_no_code(env: &Environment, name: &Name) -> bool {
    if env.get_extern(name).is_some()
        || env.has_implemented_by(name)
        || *name == Name::from_string("Quot.mk")
        || *name == Name::from_string("Quot.lift")
    {
        return false;
    }
    if env.is_noncomputable(name) || env.is_noncomputable(&name.clone().str("_unsafe_rec")) {
        return true;
    }
    if crate::io_bridge::has_runtime_implementation(env, name) {
        return false;
    }
    // Constructors and recursors have their own lowering rules, even where
    // logical storage represents their signatures as value-less constants.
    if env.get_constructor(name).is_some() || env.get_recursor(name).is_some() {
        return false;
    }
    if unknown_payload_compiler_context(env, name) {
        return true;
    }
    matches!(
        crate::source_kind::get(env, name),
        Some(clean_kernel::env::ConstantKind::Axiom)
    )
}

/// The code-generation diagnostic for the environment's declared Lean world.
pub(crate) fn noncomputable_message(env: &Environment, name: &Name) -> String {
    if unknown_payload_compiler_context(env, name) {
        return format!("failed to compile definition: source compiler context for imported `{name}` is unavailable");
    }
    if clean_olean::environment_world(env) == Some("v4.8.0") {
        return format!(
            "failed to compile definition, consider marking it as 'noncomputable' because it \
             depends on '{name}', and it does not have executable code"
        );
    }
    if env.is_noncomputable(name) || env.is_noncomputable(&name.clone().str("_unsafe_rec")) {
        format!(
            "failed to compile definition, consider marking it as 'noncomputable' because it \
             depends on '{name}', which is 'noncomputable'"
        )
    } else {
        format!("`{name}` not supported by code generator; consider marking definition as `noncomputable`")
    }
}

/// Per head constant, which argument positions Lean's compiler erases: a
/// type former (its type ends in a sort) or a proof (its type is a
/// proposition), read off the constant's own telescope.
struct Erasure<'e> {
    env: &'e Environment,
    masks: HashMap<Name, Vec<bool>>,
}

impl<'e> Erasure<'e> {
    fn new(env: &'e Environment) -> Self {
        Self {
            env,
            masks: HashMap::new(),
        }
    }

    fn erased(&mut self, head: &Name, position: usize) -> bool {
        if !self.masks.contains_key(head) {
            let mask = self.compute(head);
            self.masks.insert(head.clone(), mask);
        }
        self.masks
            .get(head)
            .and_then(|mask| mask.get(position))
            .copied()
            .unwrap_or(false)
    }

    fn compute(&self, head: &Name) -> Vec<bool> {
        let Some(info) = self.env.get_const(head) else {
            return Vec::new();
        };
        let mut ctx = LocalContext::new();
        let mut domains = Vec::new();
        let mut ty = info.type_.clone();
        loop {
            let current = ty.clone();
            let ExprKind::Pi(binder, dom, body) = current.kind() else {
                break;
            };
            let dom = dom.as_ref().clone();
            let fvar = ctx.push(Name::from_string("x"), dom.clone(), *binder);
            domains.push(dom);
            ty = body.instantiate(&Expr::fvar(fvar));
        }
        let tc = TypeChecker::with_context(self.env, ctx);
        domains
            .iter()
            .map(|dom| is_type_former(&tc, dom) || is_proposition(&tc, dom))
            .collect()
    }
}

/// Whether `ty` (a type) ends in a sort: its inhabitants are types or type
/// families, which Lean erases.
fn is_type_former(tc: &TypeChecker<'_>, ty: &Expr) -> bool {
    let mut cur = tc.whnf(ty);
    loop {
        let next = match cur.kind() {
            ExprKind::Sort(_) => return true,
            ExprKind::Pi(_, _, body) => body.as_ref().clone(),
            _ => return false,
        };
        cur = next;
    }
}

/// Whether `ty` is a proposition: its inhabitants are proofs.
fn is_proposition(tc: &TypeChecker<'_>, ty: &Expr) -> bool {
    tc.infer_type(ty)
        .is_ok_and(|sort| matches!(tc.whnf(&sort).kind(), ExprKind::Sort(level) if level.is_zero()))
}

/// Whether a declaration of type `ty` is erased whole by Lean's compiler, so
/// its value is never compiled: a proof, or a type or type family.
pub(crate) fn declaration_is_erased(env: &Environment, ty: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    is_type_former(&tc, ty) || is_proposition(&tc, ty)
}

/// The first constant `expr` uses in a computationally relevant position that
/// has no code ([`has_no_code`]). What Lean's compiler erases is skipped: a
/// binder's type, a sort, a `Π` type, every argument or `let` value that is a
/// type, a type family or a proof (read off its inferred type, under the
/// binders it sits below), the parameters of a constructor, of a recursor or
/// `casesOn` (with their motives) and of a structure projection, and the
/// arguments a head constant's telescope marks erased. A form Lean never
/// produces reports every constant it holds (over-reporting only).
pub(crate) fn uncompilable_dependency(
    env: &Environment,
    owner: &Name,
    expr: &Expr,
) -> Result<Option<Name>, CompilerError> {
    uncompilable_dependency_for(env, Some(owner), expr, false)
}

fn uncompilable_dependency_for(
    env: &Environment,
    owner: Option<&Name>,
    expr: &Expr,
    evaluation: bool,
) -> Result<Option<Name>, CompilerError> {
    let mut walk = CodeWalk {
        env,
        owner,
        csimp_names: HashMap::new(),
        expansions: Vec::new(),
        tc: TypeChecker::new(env),
        erasure: Erasure::new(env),
        seen: HashSet::new(),
        keep: Vec::new(),
        evaluation,
    };
    walk.visit(expr)
}

struct MacroExpansionFrame {
    name: Name,
    // These expressions are caller arguments, not recursive helper-body uses.
    // Entering one restores the expansion context from before its helper.
    arguments: Vec<Expr>,
}

impl MacroExpansionFrame {
    fn enters_caller_argument(&self, expression: &Expr) -> bool {
        // Substitution can put a caller's partial function in function position:
        // `apply (apply f) x` expands to `(apply f) x`. The whole application is
        // new, but its function prefix still belongs to the caller. Restore that
        // context before expanding the prefix, just as for an unchanged argument.
        let mut function = expression.strip_mdata();
        loop {
            if self
                .arguments
                .iter()
                .any(|argument| argument.strip_mdata() == function)
            {
                return true;
            }
            match function.kind() {
                ExprKind::App(head, _) => function = head.strip_mdata(),
                _ => return false,
            }
        }
    }
}

struct CodeWalk<'e> {
    evaluation: bool,
    env: &'e Environment,
    owner: Option<&'e Name>,
    csimp_names: HashMap<Name, Name>,
    expansions: Vec<MacroExpansionFrame>,
    tc: TypeChecker<'e>,
    erasure: Erasure<'e>,
    seen: HashSet<usize>,
    /// Opened roots need stable addresses before visiting them: a stack-local
    /// Expr is moved when retained, allowing a sibling to reuse its old address.
    /// Keep their heap allocations alive for the entire memoized traversal.
    keep: Vec<std::sync::Arc<Expr>>,
}

impl CodeWalk<'_> {
    fn csimp_name(&mut self, name: &Name) -> Result<Name, CompilerError> {
        if let Some(resolved) = self.csimp_names.get(name) {
            return Ok(resolved.clone());
        }
        let resolved = clean_compiler::resolve_csimp_reference(self.env, self.owner, name)?;
        self.csimp_names.insert(name.clone(), resolved.clone());
        Ok(resolved)
    }

    fn unavailable_head(
        &mut self,
        name: &Name,
        expression: &Expr,
    ) -> Result<Option<Name>, CompilerError> {
        let resolved = self.csimp_name(name)?;
        let unavailable = has_no_code(self.env, &resolved)
            // The interpreter has concrete IO actions implemented by its
            // bridge. Successful lowering establishes that implementation;
            // it does not execute it. Arguments are still checked below.
            && !(self.evaluation
                && resolved == *name
                && crate::io_bridge::expr_to_io_action(expression).is_ok());
        Ok(unavailable.then_some(resolved))
    }

    fn visit(&mut self, e: &Expr) -> Result<Option<Name>, CompilerError> {
        let caller = self
            .expansions
            .iter()
            .position(|frame| frame.enters_caller_argument(e));
        let suspended = caller.map(|at| self.expansions.split_off(at));
        let result = self.visit_inner(e);
        if let Some(frames) = suspended {
            self.expansions.extend(frames);
        }
        result
    }

    fn visit_inner(&mut self, e: &Expr) -> Result<Option<Name>, CompilerError> {
        if !self.seen.insert(std::ptr::from_ref(e) as usize) {
            return Ok(None);
        }
        if let Some(expansion) =
            clean_compiler::expand_source_macro_inline(self.env, self.owner, e)?
        {
            if self
                .expansions
                .iter()
                .any(|frame| frame.name == expansion.name)
            {
                return Err(CompilerError::InvalidExpr(format!(
                    "cyclic macro_inline expansion of {}",
                    expansion.name
                )));
            }
            self.expansions.push(MacroExpansionFrame {
                name: expansion.name,
                arguments: e.get_app_args().into_iter().cloned().collect(),
            });
            let body = std::sync::Arc::new(expansion.body);
            let result = self.visit(body.as_ref());
            self.keep.push(body);
            self.expansions.pop();
            return result;
        }
        match e.kind() {
            ExprKind::Const(name, _) => self.unavailable_head(name, e),
            ExprKind::App(..) => {
                let head = e.get_app_fn();
                let args = e.get_app_args();
                let head_name = match head.kind() {
                    ExprKind::Const(name, _) => {
                        if let Some(found) = self.unavailable_head(name, e)? {
                            return Ok(Some(found));
                        }
                        Some(self.csimp_name(name)?)
                    }
                    _ => {
                        if let Some(found) = self.visit(head)? {
                            return Ok(Some(found));
                        }
                        None
                    }
                };
                let skip = head_name
                    .as_ref()
                    .map_or(0, |name| self.erased_prefix(name));
                for (position, arg) in args.iter().enumerate() {
                    if position < skip {
                        continue;
                    }
                    if head_name
                        .as_ref()
                        .is_some_and(|name| self.erasure.erased(name, position))
                    {
                        continue;
                    }
                    if self.irrelevant(arg) {
                        continue;
                    }
                    if let Some(found) = self.visit(arg)? {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
            ExprKind::Lam(binder, ty, body) => {
                let fvar =
                    self.tc
                        .push_binder_local(Name::from_string("x"), ty.as_ref().clone(), *binder);
                let opened = std::sync::Arc::new(body.instantiate(&Expr::fvar(fvar)));
                let found = self.visit(opened.as_ref());
                self.keep.push(opened);
                self.tc.pop_binder_local();
                found
            }
            ExprKind::Let(_, ty, value, body, _) => {
                if !self.irrelevant_type(ty) {
                    if let Some(found) = self.visit(value)? {
                        return Ok(Some(found));
                    }
                }
                let fvar = self.tc.push_binder_local(
                    Name::from_string("x"),
                    ty.as_ref().clone(),
                    BinderInfo::Default,
                );
                let opened = std::sync::Arc::new(body.instantiate(&Expr::fvar(fvar)));
                let found = self.visit(opened.as_ref());
                self.keep.push(opened);
                self.tc.pop_binder_local();
                found
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => self.visit(inner),
            ExprKind::Pi(..)
            | ExprKind::Sort(_)
            | ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Lit(_) => Ok(None),
            _ => {
                let mut constants = HashSet::new();
                e.collect_constants_into(&mut constants);
                let mut constants: Vec<Name> = constants.into_iter().collect();
                constants.sort_by_key(Name::to_unambiguous_string);
                for name in constants {
                    if let Some(found) = self.unavailable_head(&name, e)? {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
        }
    }

    /// An argument Lean erases: a type, a type family or a proof.
    fn irrelevant(&mut self, arg: &Expr) -> bool {
        match self.tc.infer_type(arg) {
            Ok(ty) => self.irrelevant_type(&ty),
            Err(_) => false,
        }
    }

    /// A value of type `ty` is erased: `ty` ends in a sort or is a proposition.
    fn irrelevant_type(&self, ty: &Expr) -> bool {
        is_type_former(&self.tc, ty) || is_proposition(&self.tc, ty)
    }

    /// How many leading arguments of `head` Lean's compiler drops: a
    /// constructor's parameters; a recursor's parameters and motives; a
    /// `casesOn`'s parameters and motive; a structure projection's parameters.
    fn erased_prefix(&self, head: &Name) -> usize {
        if let Some(ctor) = self.env.get_constructor(head) {
            return ctor.num_params as usize;
        }
        if let Some(rec) = self.env.get_recursor(head) {
            return (rec.num_params + rec.num_motives) as usize;
        }
        if let clean_kernel::name::NameInner::Str(prefix, last) = head.inner() {
            if last.as_ref() == "casesOn" {
                if let Some(ind) = self.env.get_inductive(prefix) {
                    return ind.num_params as usize + 1;
                }
            }
        }
        projection_params(self.env, head)
    }
}

/// The parameters of a structure projection function `S.f`: a field of a
/// registered structure, or a definition whose value is `fun params… self =>
/// self.i` or `fun params… self => S.rec params … self` over a
/// one-constructor inductive (Clean's prelude defines `Fin.val` that way).
fn projection_params(env: &Environment, head: &Name) -> usize {
    if let clean_kernel::name::NameInner::Str(prefix, field) = head.inner() {
        let field = Name::anon().str(field.as_ref());
        if env.get_structure_field_index(prefix, &field).is_some() {
            if let Some(ind) = env.get_inductive(prefix) {
                return ind.num_params as usize;
            }
        }
    }
    let Some(value) = env.get_const(head).and_then(|info| info.value.as_ref()) else {
        return 0;
    };
    let mut lambdas = 0usize;
    let mut cur = value;
    while let ExprKind::Lam(_, _, body) = cur.kind() {
        lambdas += 1;
        cur = body.as_ref();
    }
    if lambdas == 0 {
        return 0;
    }
    let self_last = |e: &Expr| matches!(e.kind(), ExprKind::BVar(0));
    match cur.kind() {
        ExprKind::Proj(_, _, inner) if self_last(inner.as_ref()) => lambdas - 1,
        ExprKind::App(..) => {
            let args = cur.get_app_args();
            let one_ctor_rec = match cur.get_app_fn().kind() {
                ExprKind::Const(rec, _) => env.get_recursor(rec).is_some_and(|rec| {
                    env.get_inductive(&rec.inductive_name)
                        .is_some_and(|ind| ind.constructor_names.len() == 1)
                }),
                _ => false,
            };
            if one_ctor_rec && args.last().copied().is_some_and(self_last) {
                lambdas - 1
            } else {
                0
            }
        }
        _ => 0,
    }
}

/// The first `unsafe` constant any of `exprs` mentions, in name order: Lean's
/// kernel checks a safe declaration in a safe context
/// (`type_checker.cpp` `infer_constant`), where such a constant is
/// "(kernel) invalid declaration, it uses unsafe declaration".
pub(crate) fn unsafe_dependency<'a>(
    env: &Environment,
    exprs: impl IntoIterator<Item = &'a Expr>,
) -> Option<Name> {
    let mut constants = HashSet::new();
    for expr in exprs {
        expr.collect_constants_into(&mut constants);
    }
    let mut unsafe_constants: Vec<Name> = constants
        .into_iter()
        .filter(|name| env.is_unsafe(name))
        .collect();
    unsafe_constants.sort_by_key(Name::to_unambiguous_string);
    unsafe_constants.into_iter().next()
}

/// Lean's message for a safe declaration that uses an unsafe constant.
pub(crate) fn unsafe_message(name: &Name) -> String {
    format!("(kernel) invalid declaration, it uses unsafe declaration '{name}'")
}

/// Why `#eval` of `expr` (of type `ty`) is refused, as pinned Lean refuses
/// it, or `None` when it may run:
///
/// * the term depends on `sorryAx` (Lean 4.30.0-rc2: "Aborting evaluation
///   since the expression depends on the 'sorry' axiom"; 4.8.0: "cannot
///   evaluate code because … uses 'sorry'"); a closure Clean cannot read
///   (a value-less definition) is refused too, since it might;
/// * it uses a constant with no code ([`uncompilable_dependency`]);
/// * its type is a function type or a sort, which has no `Repr` / `ToString`
///   (Lean.Eval in 4.8.0) instance to display it by.
pub(crate) fn eval_refusal(env: &Environment, expr: &Expr, ty: &Expr) -> Option<String> {
    let sorry = Name::from_string("sorryAx");
    match collect_axioms_of_all(
        env,
        &Name::from_string("#eval"),
        used_constants_in_order(expr),
    ) {
        Ok(axioms) if axioms.contains(&sorry) => {
            return Some(
                "Aborting evaluation since the expression depends on the 'sorry' axiom, \
                 which can lead to runtime instability and crashes."
                    .to_string(),
            );
        }
        Ok(_) => {}
        Err(refusal) => {
            return Some(format!(
                "cannot evaluate: whether the expression depends on 'sorry' is unknown ({refusal})"
            ));
        }
    }
    match uncompilable_dependency_for(env, None, expr, true) {
        Ok(Some(name)) => return Some(noncomputable_message(env, &name)),
        Err(error) => return Some(format!("failed to compile evaluation: {error}")),
        Ok(None) => {}
    }
    let mut displayed = ty;
    while let ExprKind::MData(_, inner) = displayed.kind() {
        displayed = inner.as_ref();
    }
    if matches!(displayed.kind(), ExprKind::Pi(..) | ExprKind::Sort(_)) {
        return Some(format!(
            "could not synthesize a 'Repr' or 'ToString' instance for type\n  {}",
            crate::error_render::term(ty)
        ));
    }
    None
}

/// Diagnose compilation after registration and attribute application. Kernel
/// admission is retained on a compiler error, as in Lean's command elaborator.
pub(crate) fn diagnose_registered(
    env: &mut Environment,
    file_ctx: Option<&crate::FileContext>,
    result: crate::ElabResult,
    span: Option<clean_parser::Span>,
) -> crate::ElabResult {
    use crate::ElabResult;
    if !front_door_active() {
        return result;
    }
    if let ElabResult::Multiple(results) = result {
        return ElabResult::Multiple(
            results
                .into_iter()
                .map(|result| diagnose_registered(env, file_ctx, result, span))
                .collect(),
        );
    }
    let (name, ty, value, modifiers) = match &result {
        ElabResult::Definition {
            name,
            ty,
            val,
            modifiers,
            ..
        }
        | ElabResult::Instance {
            name,
            ty,
            val,
            modifiers,
            ..
        } => (name, ty, Some(val), modifiers),
        ElabResult::Opaque {
            name,
            ty,
            val,
            modifiers,
            ..
        } => (name, ty, val.as_ref(), modifiers),
        ElabResult::Axiom {
            name,
            ty,
            modifiers,
            ..
        } if env.get_extern(name).is_some() => (name, ty, None, modifiers),
        // A diagnosed inner leaf has already been checked in its own source scope.
        _ => return result,
    };
    if modifiers.is_noncomputable || env.is_noncomputable(name) {
        return result;
    }
    let external = env.get_extern(name).is_some();
    let replaced = env.has_implemented_by(name);
    let check_signature = name == &Name::interned("main")
        && file_ctx
            .is_some_and(|ctx| matches!(ctx.lean_world(), Ok(clean_kernel::LeanWorld::Lean436)))
        && (external
            || (!env.is_macro_inline(name) && !replaced && env.get_matcher_info(name).is_none()));
    let body = value
        .filter(|_| !modifiers.is_partial && !external && !replaced && !env.is_macro_inline(name));
    if (!check_signature && body.is_none()) || declaration_is_erased(env, ty) {
        return result;
    }
    let message = if check_signature
        && clean_compiler::main_signature::MainSignature::from_type(ty).is_none()
    {
        clean_compiler::main_signature::INVALID_MAIN_TYPE.to_owned()
    } else {
        let Some(value) = body else { return result };
        match uncompilable_dependency(env, name, value) {
            Ok(Some(dependency)) => noncomputable_message(env, &dependency),
            Err(error) => format!("failed to compile definition: {error}"),
            Ok(None) => return result,
        }
    };
    // A failed compiler task has no executable implementation. Lean retains
    // the logical declaration and marks it noncomputable for later callers.
    env.mark_noncomputable(name.clone());
    if in_noncomputable_section() {
        return result;
    }
    ElabResult::Diagnosed {
        result: Box::new(result),
        diagnostics: vec![crate::source_diagnostics::SourceDiagnostic {
            error: crate::ElabError::CommandFailed { message },
            span,
        }],
    }
}
