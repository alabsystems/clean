// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The backstop for the eager IO model: audit a declaration's kernel value —
//! AFTER `native_eager_io::rewrite_for_eager_io` — and refuse to build when an
//! action could still be evaluated anywhere Lean would not run it.
//!
//! Under the eager model evaluating an action runs it, so an action is faithful
//! exactly where evaluating it IS running it: as a function's result (a
//! declaration body, a `fun` body, a `let` body) and as the action of a `bind`.
//! This audit therefore works at every place a value is BOUND, where the kernel
//! value states the binder's type:
//!
//! * **an action passed as an argument** — to a constructor (`[IO.println "x"]`),
//!   to `pure`, to any function (`twice (IO.println "x")`) — is refused: it ran
//!   when the argument was evaluated, and Lean runs it where the callee uses
//!   it, maybe never, maybe twice (`native-eager-io`);
//! * **an action bound by a `let`** that survived ζ is refused, as is **a
//!   variable of action type** (a parameter `(a : IO Unit)`, a field of a
//!   structure): it names an action that already ran;
//! * **a branch form whose result is an action** (`ite`, `cond`,
//!   `<I>.casesOn`, `<I>.rec`) that the rewrite could not thunk is refused: its
//!   arms are evaluated arguments;
//! * **a function that returns an action**, passed to a callee whose own
//!   declared parameter type is NOT such a function (`List.map IO.println xs`),
//!   is refused: generic code may apply it where nothing sequences the result.
//!   `bind`'s continuation and the arms of the branch forms are the exceptions,
//!   because their semantics is known: they apply the function once and return
//!   the result, which this audit then checks where it lands;
//! * **`Bind.bind` / `Pure.pure` at a monad other than `IO` or `Id`** is refused
//!   (`native-monad-shim`): they stay native EXTERNS (`is_primitive_denylisted`)
//!   whose shims implement exactly one semantics — "apply the continuation to
//!   the value" — which is `IO`'s under the eager model and `Id`'s, and wrong
//!   for `Option`, `Except`, `StateM` and the rest. (They are Lean's class
//!   projections in the prelude since 2026-09-28 — instance-free axioms before,
//!   which proved `False` — so each application carries its instance argument
//!   after the monad, which the shims erase.)

use std::collections::HashSet;

use clean_kernel::{
    ConstantKind, Environment, Expr, ExprKind, FVarId, LocalContext, Name, TypeChecker,
};

use crate::native_eager_io::{
    is_action_branch_form, is_action_returning, is_action_type, is_type_like, spine,
};

/// Monads whose `Bind.bind` / `Pure.pure` the native shims implement
/// faithfully: `l_Bind_bind` applies the continuation to the (already run)
/// action's result and `l_Pure_pure` returns its argument.
const SHIMMED_MONADS: &[&str] = &["IO", "BaseIO", "Id"];

/// Why the native path refuses a declaration's `IO` code.
#[derive(Debug, thiserror::Error)]
pub(crate) enum EagerIoRefusal {
    /// An action evaluated outside a position where evaluating it is running
    /// it in Lean's order.
    #[error(
        "native build refuses `{decl}`: {what}. The native IO model is eager -- evaluating \
         an `IO` action runs it -- so this shape would run an effect when Lean does not \
         (native-eager-io)."
    )]
    Unsequenced {
        /// The declaration being audited.
        decl: String,
        /// What was found, in words.
        what: String,
    },
    /// A monad-generic prelude axiom used at a monad its shim does not
    /// implement.
    #[error(
        "native build refuses `{decl}`: `{op}` is used at the monad `{monad}`, but the \
         native `{op}` shim implements only `IO` and `Id` (native-monad-shim)."
    )]
    ForeignMonad {
        /// The declaration being audited.
        decl: String,
        /// `Bind.bind` or `Pure.pure`.
        op: String,
        /// The monad argument, rendered.
        monad: String,
    },
}

/// Constants whose presence makes a value worth auditing: the action types,
/// and the monad axioms whose monad argument must be checked.
const AUDIT_TRIGGERS: &[&str] = &["IO", "BaseIO", "EIO", "Bind.bind", "Pure.pure", "IO.bind"];

/// Could `value` hold an action, or a monadic bind whose monad must be
/// checked? A value for which this is `false` holds neither, so neither the
/// rewrite nor the audit has anything to do; every `true` only costs an audit.
///
/// It answers `true` when the value mentions
///
/// * an [`AUDIT_TRIGGERS`] constant;
/// * a constant whose TYPE yields an action — `IO.println : String → IO Unit`,
///   `act : M Unit` — or that is itself an alias of an action type former
///   (`abbrev M := IO`);
/// * a binder (`fun`, `∀`, `let`) whose type yields an action.
///
/// The syntactic trigger list alone was not enough, measured 2026-09-25 on the
/// P0_EXEC branch through `clean run` against pinned Lean v4.30.0-rc2: an
/// action passed straight to a callee that ignores it,
/// `def skip (a : IO Unit) : IO Unit := pure ()` with
/// `def main : IO Unit := skip (IO.println "a")`, has a `main` whose value
/// names only `skip` and `IO.println`, so it was never audited and printed `a`
/// at exit 0 (Lean prints nothing); and under `abbrev M := IO`,
/// `(fun (x : M Unit) => x) (if c then IO.println "a" else IO.println "b")`
/// names `M` where it would have named `IO`, so its `if` was never thunked and
/// printed `a` and `b` (Lean prints `a`).
pub(crate) fn mentions_actions(env: &Environment, value: &Expr) -> bool {
    let mut stack: Vec<&Expr> = vec![value];
    let mut seen: HashSet<*const Expr> = HashSet::new();
    let mut inert: HashSet<Name> = HashSet::new();
    while let Some(e) = stack.pop() {
        if !seen.insert(e as *const Expr) {
            continue;
        }
        match e.kind() {
            ExprKind::Const(name, _) => {
                if AUDIT_TRIGGERS.contains(&name.to_string().as_str()) {
                    return true;
                }
                if !inert.contains(name) {
                    if constant_yields_action(env, name) {
                        return true;
                    }
                    inert.insert(name.clone());
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                if yields_action(env, ty) {
                    return true;
                }
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                if yields_action(env, ty) {
                    return true;
                }
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    false
}

/// Is `ty` an action type, or a function type whose final codomain is one?
fn yields_action(env: &Environment, ty: &Expr) -> bool {
    is_action_type(env, ty) || is_action_returning(env, ty)
}

/// Does the constant `name` yield an action when applied — its type does — or
/// is it a definition whose value, under its `fun` binders, is an action type
/// or an action type former (`abbrev M := IO`, `def M α := IO α`)?
fn constant_yields_action(env: &Environment, name: &Name) -> bool {
    let Some(info) = env.get_const(name) else {
        return false;
    };
    if yields_action(env, &info.type_) {
        return true;
    }
    let Some(value) = info
        .value
        .as_ref()
        .filter(|_| info.kind == ConstantKind::Definition)
    else {
        return false;
    };
    let mut body = value.strip_mdata();
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref().strip_mdata();
    }
    let (head, _) = spine(body);
    let names_action_former = matches!(
        head.kind(),
        ExprKind::Const(head_name, _) if ACTION_TYPE_FORMERS.contains(&head_name.to_string().as_str())
    );
    names_action_former || is_action_type(env, body)
}

/// The action type formers, whose appearance at the head of a definition's
/// value makes that definition an alias of one.
const ACTION_TYPE_FORMERS: &[&str] = &["IO", "BaseIO", "EIO"];

/// Audit one declaration's (already rewritten) value.
pub(crate) fn check_eager_io(
    env: &Environment,
    decl: &Name,
    value: &Expr,
) -> Result<(), EagerIoRefusal> {
    Checker {
        env,
        decl: decl.to_string(),
        lctx: LocalContext::new(),
    }
    .walk(value)
}

struct Checker<'a> {
    env: &'a Environment,
    decl: String,
    /// The binders entered so far, instantiated as free variables so the
    /// kernel checker can type a subterm when the value does not say.
    lctx: LocalContext,
}

impl Checker<'_> {
    fn refuse(&self, what: impl Into<String>) -> EagerIoRefusal {
        EagerIoRefusal::Unsequenced {
            decl: self.decl.clone(),
            what: what.into(),
        }
    }

    fn tc(&self) -> TypeChecker<'_> {
        TypeChecker::with_context(self.env, self.lctx.clone())
    }

    /// Is `ty` an action type? Syntactic first (δ/β at the head); when the
    /// head is a local, ask the kernel for the weak head normal form, because
    /// a `let`-bound type is only visible to it.
    fn action_type(&self, ty: &Expr) -> bool {
        is_action_type(self.env, ty)
            || (self.local_head(ty) && is_action_type(self.env, &self.tc().whnf(ty)))
    }

    fn action_returning(&self, ty: &Expr) -> bool {
        is_action_returning(self.env, ty)
            || (self.local_head(ty) && is_action_returning(self.env, &self.tc().whnf(ty)))
    }

    fn local_head(&self, ty: &Expr) -> bool {
        matches!(spine(ty).0.kind(), ExprKind::FVar(_))
    }

    fn local_type(&self, id: FVarId) -> Option<Expr> {
        self.lctx.get(id).map(|decl| decl.type_.clone())
    }

    /// Enter a binder of type `ty`, returning the free variable standing for it.
    fn enter(&mut self, name: &Name, ty: &Expr, value: Option<&Expr>) -> Expr {
        let id = match value {
            Some(value) => self.lctx.push_let(name.clone(), ty.clone(), value.clone()),
            None => self
                .lctx
                .push(name.clone(), ty.clone(), clean_kernel::BinderInfo::Default),
        };
        Expr::fvar(id)
    }

    fn leave(&mut self, count: usize) {
        for _ in 0..count {
            self.lctx.pop();
        }
    }

    fn walk(&mut self, e: &Expr) -> Result<(), EagerIoRefusal> {
        match e.kind() {
            ExprKind::MData(_, inner) => self.walk(inner),
            ExprKind::Lam(..) => {
                let mut cur = e.clone();
                let mut entered = 0;
                while let ExprKind::Lam(_, ty, body) = cur.strip_mdata().kind() {
                    let (ty, body) = (ty.clone(), body.clone());
                    let fv = self.enter(&Name::anon(), &ty, None);
                    cur = body.instantiate(&fv);
                    entered += 1;
                }
                // A `fun` body runs when the closure is applied, and its value
                // is what the application returns: an action here is faithful.
                let result = self.walk(&cur);
                self.leave(entered);
                result
            }
            ExprKind::Let(name, ty, val, body, _) => {
                if self.action_type(ty) {
                    return Err(self.refuse(
                        "a `let` binds an action, which the eager model runs at the binding \
                         instead of at each use",
                    ));
                }
                self.walk(val)?;
                let fv = self.enter(name, ty, Some(val));
                let result = self.walk(&body.instantiate(&fv));
                self.leave(1);
                result
            }
            ExprKind::App(..) => self.walk_app(e),
            ExprKind::FVar(id) => match self.local_type(*id) {
                Some(ty) if self.action_type(&ty) => Err(self.refuse(
                    "it uses a variable of action type, which names an action that already ran \
                     when its value was computed",
                )),
                _ => Ok(()),
            },
            ExprKind::Const(name, _) if is_monad_axiom(name) => Err(self.refuse(format!(
                "`{name}` is used unapplied, so its monad cannot be checked"
            ))),
            ExprKind::Proj(_, _, inner) => self.walk(inner),
            _ => Ok(()),
        }
    }

    fn walk_app(&mut self, e: &Expr) -> Result<(), EagerIoRefusal> {
        let (head, args) = spine(e);
        match head.kind() {
            ExprKind::Lam(..) => self.walk_redex(head, &args),
            ExprKind::Const(name, levels) => {
                let levels: Vec<_> = levels.iter().cloned().collect();
                self.walk_const_app(name, &levels, head, &args)
            }
            ExprKind::FVar(id) => {
                let ty = self
                    .local_type(*id)
                    .ok_or_else(|| self.refuse("it applies a local the audit has no type for"))?;
                self.walk_args("a local function", &ty, Some(&ty), &args, false, None)
            }
            _ => {
                self.walk(head)?;
                let ty = self.tc().infer_type(head).map_err(|err| {
                    self.refuse(format!("the audit could not type an applied term ({err})"))
                })?;
                self.walk_args("an applied term", &ty, None, &args, false, Some(head))
            }
        }
    }

    /// `(fun x => b) a rest..`: `a` is bound to `x` — an argument like any
    /// other — and `b` is evaluated in the redex's own position.
    fn walk_redex(&mut self, head: &Expr, args: &[&Expr]) -> Result<(), EagerIoRefusal> {
        let mut cur = head.clone();
        let mut consumed = 0;
        for arg in args {
            let ExprKind::Lam(_, ty, body) = cur.strip_mdata().kind() else {
                break;
            };
            let (ty, body) = (ty.as_ref().clone(), body.as_ref().clone());
            self.walk_arg("a local function", arg, Some(&ty), Some(&ty), false, None)?;
            let fv = self.enter(&Name::anon(), &ty, Some(arg));
            cur = body.instantiate(&fv);
            consumed += 1;
        }
        let rest = Expr::apps(cur, args[consumed..].iter().map(|a| (*a).clone()));
        let result = self.walk(&rest);
        self.leave(consumed);
        result
    }

    fn walk_const_app(
        &mut self,
        name: &Name,
        levels: &[clean_kernel::Level],
        head: &Expr,
        args: &[&Expr],
    ) -> Result<(), EagerIoRefusal> {
        let text = name.to_string();
        match (text.as_str(), args) {
            // Bind.bind.{u,v} {m} [self : Bind m] {α β} (act : m α) (k : α → m β)
            ("Bind.bind", [m, _, _, _, act, k]) => {
                self.check_monad("Bind.bind", m)?;
                self.walk(act)?;
                return self.walk(k);
            }
            // IO.bind {α β} (act : IO α) (k : α → IO β)
            ("IO.bind", [_, _, act, k]) => {
                self.walk(act)?;
                return self.walk(k);
            }
            // Pure.pure.{u,v} {m} [self : Pure m] {α} (a : α)
            ("Pure.pure", [m, _, alpha, a]) => {
                self.check_monad("Pure.pure", m)?;
                let alpha = (*alpha).clone();
                return self.walk_arg("Pure.pure", a, Some(&alpha), None, false, None);
            }
            _ if is_monad_axiom(name) => {
                return Err(self.refuse(format!(
                    "`{text}` is applied to {} arguments, not saturated, so its monad and \
                     action cannot be checked",
                    args.len()
                )))
            }
            _ => {}
        }
        let owned: Vec<Expr> = args.iter().map(|a| (*a).clone()).collect();
        if is_action_branch_form(self.env, head, &owned) {
            return Err(self.refuse(format!(
                "`{text}` selects between actions, and this shape could not be thunked, so \
                 every arm is an evaluated argument"
            )));
        }
        let Some(ty) = self.env.instantiate_type(name, levels) else {
            // Not in the environment (or a level-arity mismatch): the build will
            // fail closed at link; there is no telescope to audit against.
            return args.iter().try_for_each(|a| self.walk(a));
        };
        let declared = self.env.get_const(name).map(|info| info.type_.clone());
        let selector = is_branch_selector(self.env, name);
        self.walk_args(&text, &ty, declared.as_ref(), args, selector, None)
    }

    /// Walk the arguments of a call against the callee's type telescope.
    /// `declared` is the callee's own (uninstantiated) type, when it has one:
    /// the question for a function-returning-an-action argument is what the
    /// CALLEE says the parameter is, not what this call site instantiated.
    fn walk_args(
        &mut self,
        callee: &str,
        fn_ty: &Expr,
        declared: Option<&Expr>,
        args: &[&Expr],
        selector: bool,
        applied_head: Option<&Expr>,
    ) -> Result<(), EagerIoRefusal> {
        let mut ty = Some(fn_ty.clone());
        let mut declared = declared.cloned();
        for (index, arg) in args.iter().enumerate() {
            let domain = match ty.take().and_then(|t| self.as_pi(&t)) {
                Some((domain, body)) => {
                    ty = Some(body.instantiate(arg));
                    Some(domain)
                }
                None => None,
            };
            let declared_domain = match declared.take().as_ref().map(Expr::strip_mdata) {
                Some(d) => match d.kind() {
                    ExprKind::Pi(_, dom, body) => {
                        declared = Some(body.as_ref().clone());
                        Some(dom.as_ref().clone())
                    }
                    _ => None,
                },
                None => None,
            };
            self.walk_arg(
                callee,
                arg,
                domain.as_ref(),
                declared_domain.as_ref(),
                selector,
                applied_head.map(|head| (head, index + 1)),
            )?;
        }
        Ok(())
    }

    /// Expose a `Pi` at the head of `ty`, asking the kernel for its weak head
    /// normal form when it is not syntactically one.
    fn as_pi(&self, ty: &Expr) -> Option<(Expr, Expr)> {
        let pi = |e: &Expr| match e.strip_mdata().kind() {
            ExprKind::Pi(_, d, b) => Some((d.as_ref().clone(), b.as_ref().clone())),
            _ => None,
        };
        pi(ty).or_else(|| pi(&self.tc().whnf(ty)))
    }

    fn walk_arg(
        &mut self,
        callee: &str,
        arg: &Expr,
        domain: Option<&Expr>,
        declared: Option<&Expr>,
        selector: bool,
        applied_at: Option<(&Expr, usize)>,
    ) -> Result<(), EagerIoRefusal> {
        // Attach the site only to the argument that fails its own check. A
        // failure inside the argument has its own callee and position.
        let refuse = |reason: String| match applied_at {
            Some((head, position)) => self.refuse(format!(
                "{reason} (while checking argument {position} of {})",
                applied_head_description(head)
            )),
            None => self.refuse(reason),
        };
        let domain = match domain {
            Some(d) => d.clone(),
            None => self.tc().infer_type(arg).map_err(|err| {
                refuse(format!(
                    "the audit could not type an argument of `{callee}` ({err})"
                ))
            })?,
        };
        if is_type_like(self.env, &domain) {
            return Ok(());
        }
        if self.action_type(&domain) {
            return Err(refuse(format!(
                "an action is passed as an argument to `{callee}`, so it runs when the \
                 argument is evaluated instead of where `{callee}` uses it"
            )));
        }
        if !selector
            && self.action_returning(&domain)
            && !declared.is_some_and(|d| is_action_returning(self.env, d))
        {
            return Err(refuse(format!(
                "a function returning an action is passed to `{callee}`, whose parameter is not \
                 declared as one, so `{callee}` may apply it where nothing sequences the action"
            )));
        }
        self.walk(arg)
    }

    fn check_monad(&self, op: &str, m: &Expr) -> Result<(), EagerIoRefusal> {
        let mut cur = m.strip_mdata().clone();
        for _ in 0..8 {
            let (head, _) = spine(&cur);
            let ExprKind::Const(name, levels) = head.kind() else {
                break;
            };
            if SHIMMED_MONADS.contains(&name.to_string().as_str()) {
                return Ok(());
            }
            // A transparent alias of a shimmed monad (`abbrev M := IO`).
            let Some(info) = self.env.get_const(name) else {
                break;
            };
            let (Some(value), ConstantKind::Definition) = (&info.value, info.kind) else {
                break;
            };
            if info.level_params.len() != levels.len() {
                break;
            }
            let levels: Vec<_> = levels.iter().cloned().collect();
            cur = value.instantiate_level_params_direct(&info.level_params, &levels);
        }
        Err(EagerIoRefusal::ForeignMonad {
            decl: self.decl.clone(),
            op: op.to_string(),
            monad: m.to_string(),
        })
    }
}

/// Describe the head retained by the fallback without expanding its body.
fn applied_head_description(head: &Expr) -> String {
    match head.kind() {
        ExprKind::Proj(structure, index, _) => {
            format!("projection `{structure}` field {index} (zero-based)")
        }
        ExprKind::Let(name, ..) => format!("let binding `{name}`"),
        ExprKind::BVar(index) => format!("bound variable {index}"),
        ExprKind::Sort(_) => "a sort".to_string(),
        ExprKind::Pi(..) => "a forall expression".to_string(),
        ExprKind::Lit(_) => "a literal".to_string(),
        // The spine and walk_app handle the remaining core forms.
        _ => "a non-core expression".to_string(),
    }
}

/// `Bind.bind`, `Pure.pure`, `IO.bind`: the monad axioms the native shims
/// implement by one fixed semantics.
fn is_monad_axiom(name: &Name) -> bool {
    matches!(
        name.to_string().as_str(),
        "Bind.bind" | "Pure.pure" | "IO.bind"
    )
}

/// Branch forms whose arms may be functions returning actions: each applies
/// (or returns) exactly the selected arm and nothing else, so the arm's result
/// lands wherever the branch form's own result does — which is checked there.
fn is_branch_selector(env: &Environment, name: &Name) -> bool {
    let text = name.to_string();
    matches!(text.as_str(), "ite" | "dite" | "cond")
        || text
            .strip_suffix(".casesOn")
            .is_some_and(|ind| env.get_inductive(&Name::from_string(ind)).is_some())
        || env.get_recursor(name).is_some()
}

#[cfg(test)]
#[path = "native_eager_io_check_tests.rs"]
mod tests;
