// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kan operations: head-reduction of the generalized coercion `coe^{r→s}` (and
//! `transp`, which delegates to `coe^{0→1}`). This is the computational core
//! that makes cubical equality *compute*.
//!
//! ## Soundness anchor: type preservation
//!
//! Every rule here is a **type-preserving** rewrite: with `coe A r s base : A s`
//! and `base : A r`, the reduct must also infer to `A s`. Each rule below is the
//! standard Cartesian-cubical definitional computation rule; rules that cannot be
//! discharged soundly (Sigma, Path/PathP, neutral/other heads) are left **stuck**
//! (return `None`). A stuck term is sound; a wrong reduction is not.
//!
//! ## De Bruijn discipline
//!
//! WHNF is *weak*: it never reduces under a binder. By the time a `coe` reaches
//! `try_coe_reduction`, every variable that was bound *outside* the current focus
//! has already been opened to a fresh `FVar` (binders are opened with `open_bvar`
//! before `whnf_recurse`; see `try_coe_pi` / `line_body_is_constant`). Hence the
//! carried interval endpoints `r`/`s` and the `base` contain **no loose BVars at
//! depth 0**, so re-using them under freshly introduced binders (the result
//! lambda, the codomain interval line) needs no index shifting — exactly the
//! locally-nameless invariant `try_transp_pi`-style surgery relies on.

use super::cofib::Cofib;
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::InductiveVal;
use crate::level::Level;
use crate::name::Name;
use crate::tc::whnf::WhnfMode;
use crate::tc::{TypeChecker, TypeError};
use std::sync::Arc;

/// Reserved constant names for the **Expr-encoding** of cofibrations and partial
/// element systems (Deliverable A).
///
/// ## Why an Expr-encoding (and not new `ExprKind` variants)
///
/// `CubicalHComp` keeps its field types `phi: Arc<Expr>`, `u: Arc<Expr>`. A
/// disjunctive cofibration and a multi-branch system are encoded as ordinary
/// `Const`/`App` terms over these reserved heads, so every generic traversal —
/// the visitor, substitution, `compute_meta`, the certificate builder/verifier,
/// `def_eq`, display — walks them unchanged, with **zero** new exhaustive-match
/// sites. Only this module (`parse_cofib`/`parse_system`) and the hcomp typing
/// helper interpret the encoding.
///
/// ## Typing of the encoding (so existing infer/cert machinery accepts it)
///
/// The reserved constants are registered (see [`register_kan_system_axioms`])
/// with **interval-valued** types, so the encoded `phi` genuinely has type `I`
/// and the encoded system genuinely has type `I → A`:
///
/// ```text
/// Cofib.top, Cofib.bot          : I
/// Cofib.eq0, Cofib.eq1          : I → I          -- the atomic faces (r=0)/(r=1)
/// Cofib.and, Cofib.or           : I → I → I      -- meet / join
/// System.cons.{u} {A : Sort u}  : (φ:I) → (head:I→A) → (tail:I→A) → (I→A)
/// System.nil.{u}  {A : Sort u}  : I → A          -- the empty tail terminator
/// ```
///
/// A cofibration is `Cofib.or (Cofib.eq0 i) (Cofib.eq1 i)` etc.; the legacy
/// single-face model `phi : I` (with `i1 ↦ ⊤`, `i0 ↦ ⊥`) is the special case of
/// a bare interval term parsed as the face `(phi = 1)`. A system
/// `[φ₁ ↦ u₁, …, φₙ ↦ uₙ]` is `System.cons φ₁ u₁ (… (System.cons φₙ uₙ System.nil))`;
/// the legacy single-branch model is just a bare function `u : I → A`.
pub(crate) mod kan_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static COFIB_TOP: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.top"));
    pub static COFIB_BOT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.bot"));
    pub static COFIB_EQ0: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.eq0"));
    pub static COFIB_EQ1: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.eq1"));
    pub static COFIB_AND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.and"));
    pub static COFIB_OR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Cofib.or"));
    pub static SYSTEM_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("System.cons"));
    pub static SYSTEM_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("System.nil"));
}

/// Reserved constant names for the **Expr-encoding** of Glue types and
/// univalence (`ua`) — Glue Phases 0–2 (formation + boundary + `unglue` β).
///
/// ## Why an Expr-encoding (and not a new `ExprKind::CubicalGlue` variant)
///
/// Exactly as for cofibrations/systems ([`kan_names`]): `Glue`, `glue`,
/// `unglue`, the equivalence type `Equiv`, and the Glue-system constructors
/// `Glue.Sys.cons/nil` are ordinary `Const`/`App` terms over reserved heads with
/// **interval/type-valued axiom types** (see [`register_glue_axioms`]). So the
/// visitor, substitution, `compute_meta`, the certificate builder/verifier,
/// `def_eq` and display all walk a `Glue …` / `unglue …` term as a plain
/// constant application — **zero** new exhaustive-match sites, **zero** cert
/// changes. Only this module (`parse_glue_system` / `try_glue_reduction`)
/// interprets the encoding.
///
/// ## Typing of the encoding (so existing infer/cert machinery accepts it)
///
/// ```text
/// Equiv.{u}          (A B : Sort u)                       : Sort u
/// Equiv.mk.{u}       {A B : Sort u} (f : A→B) (g : B→A)
///                      (η : (x:A)→g(f x)=x) (ε : (y:B)→f(g y)=y)  : Equiv A B
/// Equiv.idEquiv.{u}  (A : Sort u)                         : Equiv A A
/// Equiv.fwd.{u}      {A B : Sort u} : Equiv A B → A → B   -- forward-map projection
/// Glue.Sys.{u}       (B : Sort u)                         : Sort u   -- opaque type of glue-systems over B
/// Glue.Sys.nil.{u}   (B : Sort u)                         : Glue.Sys B
/// Glue.Sys.cons.{u}  (B:Sort u)(φ:I)(T:Sort u)(e:Equiv T B)(tail:Glue.Sys B) : Glue.Sys B
/// Glue.{u}           (B:Sort u)(φ:I)(sys:Glue.Sys B)      : Sort u
/// unglue.{u}         (B:Sort u)(φ:I)(sys:Glue.Sys B)(g:Glue B φ sys) : B
/// glue.{u}           (B:Sort u)(T:Sort u)(φ:I)(e:Equiv T B)(t:T)(a:B)
///                      : Glue B φ (Glue.Sys.cons B φ T e (Glue.Sys.nil B))
/// ```
///
/// A Glue system `[φ₁↦(T₁,e₁), …]` is
/// `Glue.Sys.cons B φ₁ T₁ e₁ (… Glue.Sys.nil B)`; each cell carries its own face
/// `φᵢ`, type `Tᵢ : Sort u`, and equivalence `eᵢ : Equiv Tᵢ B` (mirroring the
/// `System.cons`/`System.nil` partial-element encoding).
pub(crate) mod glue_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static EQUIV: LazyLock<Name> = LazyLock::new(|| Name::from_string("Equiv"));
    pub static EQUIV_ID: LazyLock<Name> = LazyLock::new(|| Name::from_string("Equiv.idEquiv"));
    pub static EQUIV_FWD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Equiv.fwd"));
    pub static EQUIV_BWD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Equiv.bwd"));
    pub static EQUIV_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Equiv.mk"));
    pub static EQUIV_TO_IS_EQUIV: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Equiv.toIsEquiv"));
    pub static GLUE_SYS: LazyLock<Name> = LazyLock::new(|| Name::from_string("Glue.Sys"));
    pub static GLUE_SYS_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("Glue.Sys.cons"));
    pub static GLUE_SYS_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Glue.Sys.nil"));
    pub static GLUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Glue"));
    pub static GLUE_INTRO: LazyLock<Name> = LazyLock::new(|| Name::from_string("glue"));
    pub static UNGLUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("unglue"));
}

/// Reserved constant names for the **interval connections** — the De Morgan
/// lattice structure on the interval `I`: meet `I.min`, join `I.max`, and the
/// involutive reversal `I.neg`.
///
/// ## Why an Expr-encoding (and not new `ExprKind` variants)
///
/// Exactly as for [`kan_names`] / [`glue_names`]: the three connections are
/// ordinary `Const`/`App` terms over reserved heads with **interval-valued**
/// axiom types (`I.min`, `I.max : I → I → I`; `I.neg : I → I`, registered by
/// [`register_kan_system_axioms`]). So the visitor, substitution,
/// `compute_meta`, the certificate builder/verifier, `def_eq` and display all
/// walk an `I.min …` / `I.neg …` term as a plain constant application —
/// **zero** new exhaustive-match sites, **zero** cert changes. Only
/// [`TypeChecker::try_interval_connection_reduction`] (fired by the WHNF
/// trampoline for `Const` heads in Cubical mode) interprets the encoding.
pub(crate) mod conn_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static I_MIN: LazyLock<Name> = LazyLock::new(|| Name::from_string("I.min"));
    pub static I_MAX: LazyLock<Name> = LazyLock::new(|| Name::from_string("I.max"));
    pub static I_NEG: LazyLock<Name> = LazyLock::new(|| Name::from_string("I.neg"));
}

/// Reserved constant names for the **Expr-encoding** of dependent sums (`Σ`) —
/// the type former, its pair constructor, and its (dependent) eliminator.
///
/// ## Why an Expr-encoding (and not a native `Sigma` inductive)
///
/// Exactly as for [`glue_names`] / [`kan_names`]: `Sigma`, `Sigma.mk`,
/// `Sigma.elim` are ordinary `Const`/`App` terms over reserved heads with
/// type-valued axiom types (see [`register_sigma_axioms`]), so the visitor,
/// substitution, `compute_meta`, the certificate builder/verifier, `def_eq` and
/// display all walk a `Sigma …` term as a plain constant application — **zero**
/// new exhaustive-match sites, **zero** new reduction rules. The cubical
/// `isEquiv`/`isContr`/`fiber` constructions ([`is_equiv_type`], [`is_contr_type`],
/// [`fiber_type`]) need only Σ *formation* and the *eliminator applied to a
/// variable* (never `Sigma.elim (Sigma.mk …)`), so the missing iota rule is never
/// required — which is why an axiomatic Σ suffices and stays sound.
///
/// ## Typing of the encoding (so existing infer/cert machinery accepts it)
///
/// ```text
/// Sigma.{u}      (A : Sort u) (B : A → Sort u)            : Sort u
/// Sigma.mk.{u}   (A : Sort u) (B : A → Sort u) (a:A) (b:B a) : Sigma A B
/// Sigma.elim.{u} (A : Sort u) (B : A → Sort u)
///                (M : Sigma A B → Sort u)
///                (m : (a:A) → (b:B a) → M (Sigma.mk A B a b))
///                (p : Sigma A B)                          : M p
/// ```
///
/// A **single** universe `u` (both Σ components and the motive live in `Sort u`)
/// is all the cubical `isEquiv` layer needs (the fibers/contractions stay in the
/// equivalence's own universe), which keeps the level handling trivial.
pub(crate) mod sigma_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static SIGMA: LazyLock<Name> = LazyLock::new(|| Name::from_string("Sigma"));
    pub static SIGMA_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Sigma.mk"));
    pub static SIGMA_ELIM: LazyLock<Name> = LazyLock::new(|| Name::from_string("Sigma.elim"));
}

impl<'env> TypeChecker<'env> {
    /// Intern a neutral interval term to a small `u32` id (the identity used by
    /// [`Cofib`] atoms). Structurally-equal interval terms share an id; distinct
    /// ones get distinct ids.
    ///
    /// SOUNDNESS: structural interning can only *under*-identify (give two
    /// genuinely-equal-but-syntactically-distinct variables different ids), which
    /// makes `Cofib::and`'s contradiction detection *miss* contradictions — i.e.
    /// it errs toward keeping overlaps non-empty (more agreement checks), never
    /// toward a spurious `⊥`. So it never lets `validate_hcomp_system` accept an
    /// inconsistent system. Same-id ⟺ syntactically-identical term ⟹ genuinely the
    /// same variable, so a detected contradiction is always real.
    fn intern_ivar(e: &Expr, interner: &mut Vec<Expr>) -> u32 {
        if let Some(idx) = interner.iter().position(|x| x == e) {
            idx as u32
        } else {
            interner.push(e.clone());
            (interner.len() - 1) as u32
        }
    }

    /// Parse the atomic face `(r = 0)` (`is_one = false`) or `(r = 1)`
    /// (`is_one = true`) for an interval term `r`. Literal endpoints decide the
    /// atom (`i0`/`i1 ↦ ⊤`/`⊥` as appropriate); a neutral `r` becomes a `Cofib`
    /// atom over its interned id.
    fn parse_face_atom(
        &self,
        r: &Expr,
        is_one: bool,
        interner: &mut Vec<Expr>,
        mode: WhnfMode,
    ) -> Cofib {
        let rw = self.whnf_recurse(r, mode);
        match rw.kind() {
            ExprKind::CubicalI0 => {
                if is_one {
                    Cofib::bot()
                } else {
                    Cofib::top()
                }
            }
            ExprKind::CubicalI1 => {
                if is_one {
                    Cofib::top()
                } else {
                    Cofib::bot()
                }
            }
            _ => {
                let id = Self::intern_ivar(&rw, interner);
                if is_one {
                    Cofib::eq1(id)
                } else {
                    Cofib::eq0(id)
                }
            }
        }
    }

    /// Parse a cofibration `Expr` into a [`Cofib`] (DNF face algebra).
    ///
    /// Recognises the reserved encoding (`Cofib.top/bot/eq0/eq1/and/or`) and, as
    /// the legacy single-face base case, a bare interval term `r` (read as the
    /// face `(r = 1)`, so `i1 ↦ ⊤`, `i0 ↦ ⊥`). Interval variables are interned
    /// (shared across one parse) so `and`/`or` see consistent atom ids.
    fn parse_cofib(&self, e: &Expr, interner: &mut Vec<Expr>, mode: WhnfMode) -> Option<Cofib> {
        let w = self.whnf_recurse(e, mode);
        match w.kind() {
            ExprKind::CubicalI0 => return Some(Cofib::bot()),
            ExprKind::CubicalI1 => return Some(Cofib::top()),
            _ => {}
        }
        if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
            let args = w.get_app_args();
            if *name == *kan_names::COFIB_TOP && args.is_empty() {
                return Some(Cofib::top());
            }
            if *name == *kan_names::COFIB_BOT && args.is_empty() {
                return Some(Cofib::bot());
            }
            if *name == *kan_names::COFIB_EQ0 && args.len() == 1 {
                return Some(self.parse_face_atom(args[0], false, interner, mode));
            }
            if *name == *kan_names::COFIB_EQ1 && args.len() == 1 {
                return Some(self.parse_face_atom(args[0], true, interner, mode));
            }
            if *name == *kan_names::COFIB_AND && args.len() == 2 {
                let a = self.parse_cofib(args[0], interner, mode)?;
                let b = self.parse_cofib(args[1], interner, mode)?;
                return Some(a.and(&b));
            }
            if *name == *kan_names::COFIB_OR && args.len() == 2 {
                let a = self.parse_cofib(args[0], interner, mode)?;
                let b = self.parse_cofib(args[1], interner, mode)?;
                return Some(a.or(&b));
            }
        }
        // Bare neutral interval term `r`: the legacy face `(r = 1)`. (Typing has
        // already guaranteed `r : I`, so this is a genuine interval variable.)
        Some(Cofib::eq1(Self::intern_ivar(&w, interner)))
    }

    /// Parse the partial-element **system** `(phi, u)` into its branches
    /// `[(φ₁, u₁), …, (φₙ, uₙ)]`, each `uᵢ : I → A`.
    ///
    /// * Multi-branch: `u` is `System.cons φᵢ uᵢ (… System.nil)`; each branch
    ///   carries its own face `φᵢ` and tube `uᵢ`.
    /// * Legacy single-branch: `u` is an ordinary function and the single face is
    ///   read from the `phi` field. This subsumes the original `phi : I` model.
    ///
    /// One shared interner across all branches keeps interval-variable atom ids
    /// consistent between faces (so `φᵢ ∧ φⱼ` is meaningful).
    pub(in crate::tc) fn parse_system(
        &self,
        phi: &Expr,
        u: &Expr,
        mode: WhnfMode,
    ) -> Option<Vec<(Cofib, Expr)>> {
        self.parse_system_interned(phi, u, mode)
            .map(|(branches, _)| branches)
    }

    /// Like [`Self::parse_system`] but also returns the shared interval-variable
    /// interner (atom id → the interval `Expr` it stands for). The interner lets
    /// [`Self::validate_hcomp_system`] map a `Cofib` atom back to the concrete
    /// interval term it constrains, so head agreement can be checked *on the
    /// overlap face* (substituting that term to its endpoint) rather than globally.
    pub(in crate::tc) fn parse_system_interned(
        &self,
        phi: &Expr,
        u: &Expr,
        mode: WhnfMode,
    ) -> Option<(Vec<(Cofib, Expr)>, Vec<Expr>)> {
        let mut interner: Vec<Expr> = Vec::new();
        let branches = self.parse_system_into(phi, u, mode, &mut interner)?;
        Some((branches, interner))
    }

    /// Parse a system into branches reusing a **caller-supplied** interner, so two
    /// systems can be parsed against one shared interval-variable namespace and
    /// their `Cofib`s compared meaningfully (used by the Kan-aware `hcomp`
    /// definitional comparison in `def_eq::cubical`).
    pub(in crate::tc) fn parse_system_into(
        &self,
        phi: &Expr,
        u: &Expr,
        mode: WhnfMode,
        interner: &mut Vec<Expr>,
    ) -> Option<Vec<(Cofib, Expr)>> {
        let mut branches: Vec<(Cofib, Expr)> = Vec::new();
        let mut cur = u.clone();
        loop {
            let w = self.whnf_recurse(&cur, mode);
            if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
                let args = w.get_app_args();
                if *name == *kan_names::SYSTEM_CONS && args.len() == 4 {
                    // args = [A, φ, head, tail]
                    let cof = self.parse_cofib(args[1], interner, mode)?;
                    branches.push((cof, args[2].clone()));
                    cur = args[3].clone();
                    continue;
                }
                if *name == *kan_names::SYSTEM_NIL {
                    break;
                }
            }
            // `u` is an ordinary function (legacy single-branch) — take its single
            // face from the `phi` field. Also the terminating case for a system
            // whose tail is not another `cons`.
            if branches.is_empty() {
                let cof = self.parse_cofib(phi, interner, mode)?;
                branches.push((cof, u.clone()));
            }
            break;
        }
        Some(branches)
    }

    /// Attempt one head-reduction step for `CubicalHComp { ty, phi, u, base }`.
    ///
    /// Multi-branch CCHM boundary rules (all type-preserving — `uᵢ : I → A` ⇒
    /// `uᵢ i1 : A` and `base : A`):
    /// * **On a true face** — the first branch whose cofibration `φᵢ` is `⊤`
    ///   (e.g. because the surrounding interval context substituted its variable
    ///   to the matching endpoint) determines the lid:
    ///   `hcomp {A} [… φᵢ↦uᵢ …] base ↝ uᵢ i1`. Total single-branch (`φ = ⊤`,
    ///   `hcomp ↝ u i1`) is the one-branch instance of this.
    /// * **Empty extent** `⋁ φᵢ ⇓ ⊥`: no wall is active anywhere, so the lid is
    ///   the floor — `hcomp {A} [⊥] base ↝ base`.
    ///
    /// Everything else (a neutral/partial extent that is neither total on a branch
    /// nor globally empty — e.g. the generic interior of a path composition) stays
    /// **stuck** (`None`). A stuck hcomp is sound. When several branches are
    /// simultaneously total, picking the first is canonical because
    /// `validate_hcomp_system` checked overlapping branches to agree.
    pub(in crate::tc) fn try_hcomp_reduction(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        let ExprKind::CubicalHComp { phi, u, base, .. } = e.kind() else {
            return None;
        };
        let system = self.parse_system(phi, u, mode)?;

        // (A) On a true face: first total branch fixes the lid `uᵢ i1`.
        for (cof, ui) in &system {
            if cof.is_top() {
                let i1 = Expr::from_kind(ExprKind::CubicalI1);
                return Some(Expr::app(ui.clone(), i1));
            }
        }

        // (B) Empty extent: the disjunction of all faces is `⊥` ⇒ lid = floor.
        let overall = system.iter().fold(Cofib::bot(), |acc, (c, _)| acc.or(c));
        if overall.is_bot() {
            return Some(base.as_ref().clone());
        }

        // (C) Genuinely-stuck extent (φ neither ⊤ nor ⊥):
        //   * floor **type** a universe `Sort ℓ`  ⇒  `hcomp`-in-a-universe ↝ `Glue`
        //     (Deliverable A — the homogeneous composite of *types* is a Glue);
        //   * else if the floor is a constructor of a *non-HIT* inductive, `hcomp`
        //     commutes with the constructor (the CCHM Kan structure on a data type).
        if let Some(glue) = self.try_hcomp_universe_glue(e, mode) {
            return Some(glue);
        }
        self.try_hcomp_constructor_reduction(e, mode)
    }

    /// `hcomp`-in-a-**universe** ↝ `Glue` (Deliverable A — the CCHM computation of a
    /// homogeneous composite *of types*):
    ///
    /// ```text
    /// hcomp {Sort ℓ} [ φᵢ ↦ Tᵢ ] A   ↝   Glue A [ φᵢ ↦ (Tᵢ i1, coeEquiv Tᵢ) ]
    /// ```
    ///
    /// Fires only when the element type is a universe `Sort ℓ` and the extent is
    /// genuinely **neutral** (the on-a-true-face rule (A) and the empty-extent rule
    /// (B) have already been tried in [`Self::try_hcomp_reduction`], so a `Sort`
    /// floor reaching here has φ neither ⊤ nor ⊥). Each system cell carries a tube
    /// of *types* `Tᵢ : I → Sort ℓ`; the Glue cell uses the tube's lid `Tᵢ i1` as
    /// its glued type and `coeEquiv Tᵢ : Equiv (Tᵢ i1) (Tᵢ i0)` as its
    /// equivalence (built by [`coe_equiv`] purely from the existing `coe`
    /// primitive — no new axiom, no new reduction rule).
    ///
    /// ## Soundness — the `coeEquiv Tᵢ` cell argument
    ///
    /// On the face φᵢ a well-formed `hcomp` system tube agrees with the floor at the
    /// `j = i0` end: `Tᵢ i0 ≡ A`. Hence **on φᵢ** the built equivalence has the
    /// type the Glue cell demands:
    /// `coeEquiv Tᵢ : Equiv (Tᵢ i1) (Tᵢ i0) ≡ Equiv (Tᵢ i1) A`. So the produced
    /// `Glue A [φᵢ↦(Tᵢ i1, coeEquiv Tᵢ)]` is exactly the CCHM "Glue from a
    /// homogeneous composite of types", and the rewrite is type-preserving at the
    /// result-type level: `hcomp {Sort ℓ} … : Sort ℓ` and `Glue A … : Sort ℓ`.
    ///
    /// ## Boundary coherence (why it agrees with the other `hcomp` rules)
    ///
    /// On a face φᵢ ⇓ ⊤ the existing on-a-true-face rule (A) already fires and
    /// returns `Tᵢ i1`; the `Glue` boundary rule on the same total cell also reduces
    /// `Glue A [φᵢ↦(Tᵢ i1, …)]` to `Tᵢ i1` (see [`Self::try_glue_reduction`]). The
    /// two agree, so introducing the `Glue` on a *neutral* extent never disagrees
    /// with the degenerate-extent value. A `Sort` floor whose system cannot be
    /// parsed stays **stuck** (`None`), which is sound.
    fn try_hcomp_universe_glue(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        // Cubical-only — mirrors `try_hcomp_constructor_reduction` / the `ua` rule.
        if !self.mode.has_cubical_layer() {
            return None;
        }
        let ExprKind::CubicalHComp { ty, phi, u, base } = e.kind() else {
            return None;
        };
        // The element type must be a universe `Sort ℓ` (an `hcomp` *of types*).
        let ty_w = self.whnf_recurse(ty, mode);
        let ExprKind::Sort(level) = ty_w.kind() else {
            return None;
        };
        let level = level.clone();
        // Translate the partial-element system of types into a Glue system of
        // (cell-type, equivalence) cells over the Glue base `A = base`.
        let glue_sys = self.hcomp_system_to_glue_system(u, phi, base, &level, mode)?;
        // `Glue A φ glue_sys : Sort ℓ` (the floor `A = base` is the Glue base; the
        // overall extent `φ` is reused verbatim — it is interval-valued and the
        // Glue boundary rule reads the per-cell faces, not this field).
        Some(Expr::apps(
            Expr::const_(glue_names::GLUE.clone(), vec![level]),
            [base.as_ref().clone(), phi.as_ref().clone(), glue_sys],
        ))
    }

    /// Translate an `hcomp` partial-element **system of types**
    /// `[ φᵢ ↦ (Tᵢ : I → Sort ℓ) ]` into a **Glue system**
    /// `[ φᵢ ↦ (Tᵢ i1, coeEquiv Tᵢ) ]` over the Glue base `b_base` (the `hcomp`
    /// floor `A`), preserving every face φᵢ. Used by
    /// [`Self::try_hcomp_universe_glue`].
    ///
    /// Mirrors [`Self::project_system_tubes`]: recognises the
    /// `System.cons`/`System.nil` encoding (multi-branch) and the legacy bare
    /// single-tube form (whose face is the `hcomp`'s `phi` field). Returns `None`
    /// (⇒ caller stays stuck, which is sound) for an unrecognised system head.
    ///
    /// `coe_equiv`/`App(Tᵢ, i1)` are placed at the same focus as the system (no new
    /// outer binder), and the tube `Tᵢ` is a complete subterm there (no loose
    /// `BVar` at depth 0), so [`coe_equiv`]'s closed-`line` precondition holds.
    fn hcomp_system_to_glue_system(
        &self,
        u: &Expr,
        phi_fallback: &Expr,
        b_base: &Expr,
        level: &Level,
        mode: WhnfMode,
    ) -> Option<Expr> {
        let i1 = || Expr::from_kind(ExprKind::CubicalI1);
        // Glue.Sys.cons.{ℓ} B φᵢ (Tᵢ i1) (coeEquiv Tᵢ) (isEquivCoe Tᵢ) tail.
        //
        // The carried witness `is_equiv_coe(level, Tᵢ) : isEquiv (λx. coe Tᵢ i1 i0 x)`
        // is **defeq** to the demanded `isEquiv (Equiv.fwd (coeEquiv Tᵢ))`, because
        // `Equiv.fwd (coeEquiv Tᵢ) ↝ λx. coe Tᵢ i1 i0 x` (the `Equiv.fwd`-β on the
        // `Equiv.mk` that `coe_equiv` builds). Unlike the opaque `ua`-cell witness,
        // this one is a genuine **computing** `coe`-of-`idIsEquiv` proof, so the
        // residual rule's fibre centre `(isEquivCoe Tᵢ@s a₁).fst` reduces concretely.
        let glue_cell = |face: Expr, tube: &Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(glue_names::GLUE_SYS_CONS.clone(), vec![level.clone()]),
                [
                    b_base.clone(),
                    face,
                    Expr::app(tube.clone(), i1()),
                    coe_equiv(tube, level.clone()),
                    is_equiv_coe(level.clone(), tube),
                    tail,
                ],
            )
        };
        let nil = || {
            Expr::app(
                Expr::const_(glue_names::GLUE_SYS_NIL.clone(), vec![level.clone()]),
                b_base.clone(),
            )
        };

        let w = self.whnf_recurse(u, mode);
        if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
            let args = w.get_app_args();
            if *name == *kan_names::SYSTEM_CONS && args.len() == 4 {
                // args = [A(=Sort ℓ), φ, head(=Tᵢ : I→Sort ℓ), tail]
                let tail =
                    self.hcomp_system_to_glue_system(args[3], phi_fallback, b_base, level, mode)?;
                return Some(glue_cell(args[1].clone(), args[2], tail));
            }
            if *name == *kan_names::SYSTEM_NIL {
                return Some(nil());
            }
        }
        // Legacy single-branch: `u` is a bare tube `I → Sort ℓ`; its face is the
        // `hcomp`'s overall `phi` field.
        Some(glue_cell(phi_fallback.clone(), u, nil()))
    }

    /// `hcomp`-commutes-with-constructors — the CCHM Kan reduction that pushes a
    /// genuinely-stuck `hcomp` (φ neither ⊤ nor ⊥) through the constructors of a
    /// **non-higher** inductive floor (Step 6):
    ///
    /// ```text
    /// hcomp {I} [φ ↦ u] (c a₁ … aₙ)  ↝  c a₁′ … aₙ′,
    ///   where aᵢ′ = hcomp {Aᵢ} [φ ↦ projᵢ(u)] aᵢ
    /// ```
    ///
    /// This is the standard definitional computation rule of Cartesian-cubical
    /// type theory (exactly Cubical Agda's `hcomp` on a data type): the Kan
    /// composition structure on an inductive is *defined* by commuting with its
    /// constructors. It is a type-preserving rewrite (`c a₁′…aₙ′ : I`).
    ///
    /// ## Soundness
    ///
    /// * **Boundary coherence** (why projᵢ is well-defined): on the face φ each
    ///   tube `headₖ` agrees with the floor `c a₁…aₙ`, and a non-HIT inductive
    ///   satisfies *no-confusion* — every element of `I` on φ that is connected to
    ///   `c (…)` is again `c (…)` with the **same** constructor. So `projᵢ(headₖ)`
    ///   genuinely extracts the i-th argument there, and `c a₁′…aₙ′` restricts on φ
    ///   to `u i1`, matching rule (A). For a HIT this fails (a *path* constructor
    ///   can connect distinct point constructors), so the rule is **gated** to
    ///   non-HIT inductives via [`Self::inductive_has_path_constructor`].
    /// * **Scope** (partial but sound — a stuck `hcomp` is always sound): three
    ///   constructor shapes are handled; everything else stays stuck.
    ///   1. **Nullary** constructor `c` (no fields) ↝ the floor unchanged
    ///      (`hcomp {I} [φ↦u] c ↝ c`); there are no arguments to project. General
    ///      over any non-HIT inductive.
    ///   2. **Single self-recursive field** (`Nat.succ`-like: one field, recursive,
    ///      field type ≡ `I`) ↝ `c (hcomp {I} [φ↦ map projᵢ u] aᵢ)`, where the
    ///      projection `projᵢ : I → I` is the recursor-built predecessor
    ///      ([`Self::build_self_recursive_field_projection`]). Scoped to
    ///      non-parametric, non-indexed, no-level-param inductives whose other
    ///      constructors are all nullary (e.g. `Nat`), so every recursor minor is
    ///      either the projected field or a canonical default — no fabricated
    ///      inhabitant is ever required.
    ///   3. **Single non-recursive field** (`MyZ.ofNat : MyNat → MyZ`-like: one
    ///      field, type `F ≠ I`) ↝ `c (hcomp {F} [φ↦ map projᵢ u] aᵢ)`, where the
    ///      inner `hcomp` runs at the **field** type `F` (the System is re-typed
    ///      from `I` to `F`, [`Self::project_system_retype`]) and the projection
    ///      `projᵢ : I → F` ([`Self::build_single_field_projection`]) extracts the
    ///      field. Scoped to inductives whose **every** constructor has exactly one
    ///      field of (closed) type `F`, so each recursor minor is `λ(f:F).f` — no
    ///      fabricated inhabitant of `F` is ever required.
    ///
    /// Multi-field constructors, parametric/indexed inductives, and Prop-only
    /// recursors are all left **stuck** (`None`).
    fn try_hcomp_constructor_reduction(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        // Cubical-only — this is a cubical Kan reduction (mirrors the gating of
        // `try_coe_glue_compute`). `hcomp` is meaningless outside Cubical mode.
        if !self.mode.has_cubical_layer() {
            return None;
        }
        let ExprKind::CubicalHComp { ty, phi, u, base } = e.kind() else {
            return None;
        };

        // Expose the floor's head: it must be a constructor application `c ā`.
        // A `Nat` floor WHNFs to the *literal* optimization (`succ zero ↝ Lit 1`),
        // not a `Const`-headed spine — rewrite it back to constructor view first so
        // the generic logic below applies uniformly.
        let base_whnf0 = self.whnf_recurse(base, mode);
        let base_whnf = Self::nat_literal_to_ctor_form(&base_whnf0).unwrap_or(base_whnf0);
        let head = base_whnf.get_app_fn();
        let ExprKind::Const(ctor_name, ctor_levels) = head.kind() else {
            return None;
        };
        let ctor = self.env.get_constructor(ctor_name)?;
        let ind_name = ctor.inductive_name.clone();
        let ind = self.env.get_inductive(&ind_name)?;

        // GATE: non-HIT only. A higher inductive (any *path* constructor) does NOT
        // satisfy no-confusion, so the commutation is unsound there — stay stuck.
        if self.inductive_has_path_constructor(ind) {
            return None;
        }
        // SCOPE: non-parametric, non-indexed inductives keep the projection sound
        // and simple (no parameter/index plumbing). Anything else stays stuck.
        if ind.num_params != 0 || ind.num_indices != 0 || !ind.level_params.is_empty() {
            return None;
        }

        let args = base_whnf.get_app_args();
        let num_fields = ctor.num_fields as usize;
        // With no parameters, the spine args are exactly the constructor fields.
        if args.len() != num_fields {
            return None;
        }

        // (1) Nullary constructor: nothing to project — the floor is the lid.
        if num_fields == 0 {
            return Some(base_whnf.clone());
        }

        // (2) Single self-recursive field (Nat.succ-like). Other shapes: stuck.
        if num_fields != 1 {
            return None;
        }
        let rec_name = Name::append(&ind_name, "rec");
        let rec = self.env.get_recursor(&rec_name)?;
        // Large elimination must be available: a large-elim recursor carries one
        // extra (motive-universe) level param beyond the inductive's own. A
        // Prop-only recursor cannot eliminate into the (Type-valued) field — stuck.
        if rec.level_params.len() != ind.level_params.len() + 1 {
            return None;
        }
        let rule = rec
            .rules
            .iter()
            .find(|r| r.constructor_name == *ctor_name)?;
        // Exactly one field (the only single-field shapes are handled).
        if rule.recursive_fields.len() != 1 {
            return None;
        }
        // The single field's type is the first (and only) Pi domain of the
        // constructor's type (non-parametric, non-indexed ⇒ no params before it).
        let ExprKind::Pi(_, field_ty, _) = ctor.type_.kind() else {
            return None;
        };

        if rule.recursive_fields[0] {
            // (2a) Single **self-recursive** field (`Nat.succ`-like). The field
            // type must be **exactly** the inductive `I` (NOT a *reflexive* field
            // such as `X → I`: the projection `λ f ih. f` returns the field, which
            // must have the motive's result type `I`). A reflexive/nested recursive
            // field is left stuck (its projection would be ill-typed). The inner
            // `hcomp` runs at the same element type `ty` (= `I`), so the System is
            // reused unchanged.
            if !matches!(field_ty.kind(), ExprKind::Const(n, _) if *n == ind_name) {
                return None;
            }
            let proj = self.build_self_recursive_field_projection(ind, ctor_name, &rec_name)?;
            let proj_u = self.project_system_tubes(u, &proj, mode)?;
            let inner = Expr::from_kind(ExprKind::CubicalHComp {
                ty: ty.clone(),
                phi: phi.clone(),
                u: Arc::new(proj_u),
                base: Arc::new(args[0].clone()),
            });
            return Some(Expr::app(
                Expr::const_(ctor_name.clone(), ctor_levels.clone()),
                inner,
            ));
        }

        // (2b) Single **non-recursive** field (`MyZ.ofNat : MyNat → MyZ`-like):
        // `c : F → I` with the field type `F ≠ I`. The inner `hcomp` runs at the
        // FIELD type `F` (a different type from the floor's `I`), so the System
        // must be re-typed from `I` to `F`:
        //
        // ```text
        // hcomp {I} [φ↦u] (c a)  ↝  c (hcomp {F} [φ↦ λj. projᵢ(u j)] a)
        // ```
        //
        // The projection `projᵢ : I → F` extracts the single field. Both the redex
        // and the reduct have type `I` (`hcomp {F} … : F`, `c (…) : I`); on a face
        // φ⇓⊤ both routes give `c (u i1 's field)` — boundary-coherent (see method
        // note: tubes are `c`-headed on φ by no-confusion, so `projᵢ` extracts the
        // field genuinely). `F` must be closed (a concrete field type) so the
        // projection/motive are well-formed without de Bruijn surgery.
        let field_ty = field_ty.as_ref().clone();
        if field_ty.has_loose_bvars() {
            return None;
        }
        let inner_level = self.infer_sort(&field_ty).ok()?;
        let proj =
            self.build_single_field_projection(ind, ctor_name, &rec_name, &field_ty, &inner_level)?;
        let proj_u = self.project_system_retype(u, &proj, &field_ty, &inner_level, mode)?;
        let inner = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(field_ty),
            phi: phi.clone(),
            u: Arc::new(proj_u),
            base: Arc::new(args[0].clone()),
        });
        Some(Expr::app(
            Expr::const_(ctor_name.clone(), ctor_levels.clone()),
            inner,
        ))
    }

    /// Whether `ind` is a Higher Inductive Type — i.e. has at least one *path*
    /// constructor (a constructor whose return type is a `CubicalPath`, like S¹'s
    /// `loop`). Mirrors `Environment::has_path_constructor`; used to gate the
    /// constructor-commutation `hcomp` rule to genuine (non-higher) data types.
    fn inductive_has_path_constructor(&self, ind: &InductiveVal) -> bool {
        ind.constructor_names.iter().any(|cn| {
            self.env.get_constructor(cn).is_some_and(|cv| {
                matches!(
                    crate::inductive::get_return_type(&cv.type_).kind(),
                    ExprKind::CubicalPath { .. }
                )
            })
        })
    }

    /// Build the recursor-based projection `projᵢ : I → I` extracting the single
    /// self-recursive field of `target_ctor` (the "predecessor"). Scoped to a
    /// non-parametric, non-indexed, no-level-param inductive `I` whose every other
    /// constructor is **nullary**, so each recursor minor is either the projected
    /// field (for the target) or the constructor itself (a canonical default
    /// inhabitant of `I`) — no fabricated inhabitant is ever needed.
    ///
    /// ```text
    /// projᵢ := I.rec.{l} (λ _:I. I)  [ minor per ctor, in declaration order ]
    ///   target ctor  c (single recursive field) :  λ (f:I) (ih:I). f
    ///   nullary ctor c′                          :  c′
    /// ```
    ///
    /// SOUNDNESS: the projection is the standard `Nat.pred`-shaped recursor term.
    /// Its only *used* behaviour is `projᵢ (c a) ↝ a` (the recursor's iota rule on
    /// the target constructor returns the field binder), which is exactly what the
    /// boundary-coherence argument requires on the face φ where each tube is `c (…)`.
    /// The other branches' values are irrelevant (off-face) but type-correct.
    /// Returns `None` (⇒ the caller stays stuck) for any shape outside this scope.
    fn build_self_recursive_field_projection(
        &self,
        ind: &InductiveVal,
        target_ctor: &Name,
        rec_name: &Name,
    ) -> Option<Expr> {
        // The inductive's universe: `I : Sort l` (non-indexed ⇒ a bare `Sort`).
        let ExprKind::Sort(l) = ind.type_.kind() else {
            return None;
        };
        // Recursor levels: [motive-universe, …ind level params]; scoped to none.
        let rec_levels = vec![l.clone()];
        let ind_const = Expr::const_(ind.name.clone(), Vec::<Level>::new());

        // motive = λ _:I. I  (projection result type is the field type ≡ I).
        let motive = Expr::lam(BinderInfo::Default, ind_const.clone(), ind_const.clone());
        let mut rec_app = Expr::app(Expr::const_(rec_name.clone(), rec_levels), motive);

        // One minor per constructor, in declaration (= recursor minor) order.
        for cn in &ind.constructor_names {
            let cv = self.env.get_constructor(cn)?;
            let minor = if cn == target_ctor {
                // Target's minor type is `Π (f:I) (ih:I). I` (one field, one IH);
                // return the field binder `f` (BVar 1 under the two λs).
                Expr::lam(
                    BinderInfo::Default,
                    ind_const.clone(),
                    Expr::lam(BinderInfo::Default, ind_const.clone(), Expr::bvar(1)),
                )
            } else if cv.num_fields == 0 {
                // Nullary other constructor: its minor type is `I`; the
                // constructor itself is the canonical default inhabitant.
                Expr::const_(cn.clone(), Vec::<Level>::new())
            } else {
                // A non-nullary, non-target constructor would need a fabricated
                // default of the field type — refuse (caller stays stuck).
                return None;
            };
            rec_app = Expr::app(rec_app, minor);
        }
        Some(rec_app)
    }

    /// Rebuild the partial-element system `u`, replacing each tube function
    /// `headₖ : I → I` by its projection `λ j. proj (headₖ j)` (the per-argument
    /// system `projᵢ(u)`), preserving every face and the `System.cons`/`System.nil`
    /// structure. For a self-recursive field the element type is unchanged (`I`),
    /// so the `System.cons` head constant and its `{A}` argument are kept verbatim.
    ///
    /// `proj` is closed; tubes are closed at the `hcomp` focus — both are
    /// `lift`ed by one when placed under the freshly-introduced tube binder, which
    /// is a no-op for closed terms and defensively correct otherwise.
    fn project_system_tubes(&self, u: &Expr, proj: &Expr, mode: WhnfMode) -> Option<Expr> {
        let w = self.whnf_recurse(u, mode);
        if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
            let args = w.get_app_args();
            if *name == *kan_names::SYSTEM_CONS && args.len() == 4 {
                // args = [A, φ, head, tail]
                let new_head = Self::compose_proj_tube(args[2], proj);
                let new_tail = self.project_system_tubes(args[3], proj, mode)?;
                return Some(Expr::apps(
                    w.get_app_fn().clone(),
                    [args[0].clone(), args[1].clone(), new_head, new_tail],
                ));
            }
            if *name == *kan_names::SYSTEM_NIL {
                return Some(w.clone());
            }
        }
        // Legacy single-branch: `u` is a bare tube function `I → I`.
        Some(Self::compose_proj_tube(u, proj))
    }

    /// Build the recursor-based projection `projᵢ : I → F` extracting the single
    /// **non-recursive** field of `target_ctor` (`MyZ.ofNat`-like), where `F` is
    /// the field type and `field_level` its universe. Used by the constructor-
    /// commutation `hcomp` rule (case 2b) to push a stuck `hcomp` through a
    /// single-non-recursive-field constructor.
    ///
    /// ```text
    /// projᵢ := I.rec.{field_level} (λ _:I. F)  [ λ (f:F). f  per constructor ]
    /// ```
    ///
    /// SCOPE (partial but sound): every constructor of `I` must have **exactly one
    /// field whose type is def-eq to `F`** (e.g. `MyZ.ofNat : MyNat → MyZ`,
    /// `MyZ.negSucc : MyNat → MyZ`). Then each recursor minor is the identity
    /// `λ (f:F). f` — total and well-typed — so the projection needs **no
    /// fabricated default inhabitant** of `F`. Any other shape (a constructor
    /// with ≠1 field, or a field type ≢ `F`, or a non-closed field type) returns
    /// `None` (⇒ the caller stays stuck, which is sound).
    ///
    /// SOUNDNESS: the only behaviour the caller relies on is `projᵢ (c f) ↝ f`
    /// (the recursor's iota rule applies the constructor's minor `λ(f:F).f` to the
    /// field), which holds for **every** constructor here — in particular the
    /// target. On the face φ where each tube is `target`-headed (no-confusion,
    /// non-HIT), `projᵢ` extracts the genuine field; the off-face minors are
    /// type-correct but irrelevant.
    fn build_single_field_projection(
        &self,
        ind: &InductiveVal,
        _target_ctor: &Name,
        rec_name: &Name,
        field_ty: &Expr,
        field_level: &Level,
    ) -> Option<Expr> {
        // `F` must be closed so the motive `λ _:I. F` and minors `λ (f:F). f` need
        // no de Bruijn shifting.
        if field_ty.has_loose_bvars() {
            return None;
        }
        let ind_const = Expr::const_(ind.name.clone(), Vec::<Level>::new());
        // motive = λ _:I. F  (eliminate into the field type `F : Sort field_level`).
        let motive = Expr::lam(BinderInfo::Default, ind_const, field_ty.clone());
        // Recursor levels: [motive-universe] = [field_level]; scoped to no ind
        // level params (checked by the caller).
        let rec_levels = vec![field_level.clone()];
        let mut rec_app = Expr::app(Expr::const_(rec_name.clone(), rec_levels), motive);

        // One minor per constructor, in declaration (= recursor minor) order. Each
        // must be a single non-recursive field of type `F`, giving minor `λ(f:F).f`.
        for cn in &ind.constructor_names {
            let cv = self.env.get_constructor(cn)?;
            if cv.num_fields != 1 {
                return None;
            }
            // The field's type: first Pi domain of the ctor type (non-parametric).
            let ExprKind::Pi(_, dom, _) = cv.type_.kind() else {
                return None;
            };
            if dom.has_loose_bvars() || !self.is_def_eq(dom, field_ty) {
                return None;
            }
            // minor type (motive `λ_.F`, non-recursive single field): `Π(f:F). F`.
            let minor = Expr::lam(BinderInfo::Default, field_ty.clone(), Expr::bvar(0));
            rec_app = Expr::app(rec_app, minor);
        }
        Some(rec_app)
    }

    /// Project **and re-type** the partial-element system `u` for the
    /// non-recursive-field constructor-commutation rule (case 2b): replace each
    /// tube `headₖ : I → I` by `λ j. proj (headₖ j) : I → F`, and rebuild every
    /// `System.cons`/`System.nil` cell at the **field** element type `new_ty` (= F)
    /// and level `new_level` — because the inner `hcomp` runs at `F`, not the floor
    /// type `I`. Each cell's face is preserved verbatim.
    ///
    /// `proj` is closed; tubes are closed at the `hcomp` focus — both are `lift`ed
    /// by one when placed under the freshly-introduced tube binder (a no-op for
    /// closed terms, defensively correct otherwise).
    fn project_system_retype(
        &self,
        u: &Expr,
        proj: &Expr,
        new_ty: &Expr,
        new_level: &Level,
        mode: WhnfMode,
    ) -> Option<Expr> {
        let w = self.whnf_recurse(u, mode);
        if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
            let args = w.get_app_args();
            if *name == *kan_names::SYSTEM_CONS && args.len() == 4 {
                // args = [A, φ, head, tail]  →  [F, φ, λj.proj(head j), retype(tail)]
                let new_head = Self::compose_proj_tube(args[2], proj);
                let new_tail =
                    self.project_system_retype(args[3], proj, new_ty, new_level, mode)?;
                let cons = Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![new_level.clone()]);
                return Some(Expr::apps(
                    cons,
                    [new_ty.clone(), args[1].clone(), new_head, new_tail],
                ));
            }
            if *name == *kan_names::SYSTEM_NIL {
                let nil = Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![new_level.clone()]);
                return Some(Expr::app(nil, new_ty.clone()));
            }
        }
        // Legacy single-branch: `u` is a bare tube function `I → I`; project to
        // `λ j. proj (u j) : I → F` (the element type lives in the tube body).
        Some(Self::compose_proj_tube(u, proj))
    }

    /// Rewrite a **Nat literal** floor back to its constructor view so the generic
    /// constructor-commutation logic applies. The literal folding `succ zero ↝ Lit 1`
    /// is a Nat-specific WHNF optimization that would otherwise hide the
    /// constructor head; this is the same definitional unfolding `def_eq` uses
    /// (`Lit n ≡ Nat.succ (Lit (n-1))`, `Lit 0 ≡ Nat.zero`), so it is sound.
    /// Returns `None` for any non-`Nat`-literal expression (left unchanged).
    fn nat_literal_to_ctor_form(e: &Expr) -> Option<Expr> {
        if !matches!(e.kind(), ExprKind::Lit(crate::expr::Literal::Nat(_))) {
            return None;
        }
        if Self::is_nat_zero_expr(e) {
            return Some(Expr::const_(
                super::names::NAT_ZERO.clone(),
                Vec::<Level>::new(),
            ));
        }
        let pred = Self::is_nat_succ_expr(e)?;
        Some(Expr::app(
            Expr::const_(super::names::NAT_SUCC.clone(), Vec::<Level>::new()),
            pred,
        ))
    }

    /// `head ↦ λ (j:I). proj (head j)` — eta-expand and post-compose the tube
    /// `head : I → I` with the field projection `proj : I → I`. Both `head` and
    /// `proj` are `lift`ed past the introduced binder (no-op when closed).
    fn compose_proj_tube(head: &Expr, proj: &Expr) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::CubicalInterval),
            Expr::app(proj.lift(1), Expr::app(head.lift(1), Expr::bvar(0))),
        )
    }

    /// Validate the partial-element system of an `hcomp` for **overlap
    /// agreement** (Deliverable A): on every non-empty overlap `φᵢ ∧ φⱼ`, the
    /// tubes `uᵢ` and `uⱼ` must be definitionally equal.
    ///
    /// Called from both inference paths (the release fast path
    /// `infer_cubical_hcomp` and the debug certificate builder); the per-branch
    /// typing (`uᵢ : I → A`) is already enforced by the encoding's axiom types, so
    /// this only adds the well-formedness check the typing cannot see.
    ///
    /// SOUNDNESS: the check is **conservative** — it compares the *whole* tube
    /// functions (`is_def_eq(uᵢ, uⱼ)`), not the restriction of the tubes to the
    /// overlap face. Full equality implies equality on the overlap, so an
    /// accepted system is genuinely consistent (never a false accept). It is
    /// *incomplete* (it may reject a system whose tubes agree only on the
    /// sub-face), which is sound: rejecting is always safe. A system Clean cannot
    /// parse is left to the ordinary typing checks (we add nothing).
    pub(in crate::tc) fn validate_hcomp_system(
        &self,
        phi: &Expr,
        u: &Expr,
        _ty: &Expr,
    ) -> Result<(), TypeError> {
        let (system, interner) = match self.parse_system_interned(phi, u, WhnfMode::Full) {
            Some(s) => s,
            None => return Ok(()),
        };
        for i in 0..system.len() {
            for j in (i + 1)..system.len() {
                let overlap = system[i].0.and(&system[j].0);
                if overlap.is_bot() {
                    continue;
                }
                // CCHM adjacency: overlapping tubes need only agree **on their
                // overlap face**, not globally. Accept either when the heads are
                // globally def-eq (fast path) or when they agree restricted to
                // every disjunct of the overlap cofibration.
                if self.is_def_eq(&system[i].1, &system[j].1)
                    || self.heads_agree_on_face(&system[i].1, &system[j].1, &overlap, &interner)
                {
                    continue;
                }
                return Err(TypeError::TypeMismatch {
                    expected: Box::new(system[i].1.clone()),
                    inferred: Box::new(system[j].1.clone()),
                    location: None,
                });
            }
        }
        Ok(())
    }

    /// Validate the **cap / floor-agreement** side condition of an `hcomp`
    /// (the CCHM well-formedness constraint): on every active branch face `φᵢ`,
    /// the tube's `i0`-end must agree with the floor — `uᵢ i0 ≡ base` **restricted
    /// to `φᵢ`**.
    ///
    /// SOUNDNESS: this is the constraint *every* `hcomp` reduction rule silently
    /// assumes. On a true face the lid is `uᵢ i1`, whose `i0`-boundary is `uᵢ i0`;
    /// that boundary must equal the floor `base` for the square's faces to match.
    /// Without this check a floor-disagreeing `hcomp` such as
    /// `hcomp {Nat} [(j=1) ↦ λ_. succ zero] zero` type-checks, and `<j>` of it
    /// inhabits `Path Nat 0 1` — from which a closed proof of `Empty` follows
    /// (the reported soundness hole). It is **type-preservation-adjacent**: the
    /// boundary the reductions rely on is exactly what is enforced here.
    ///
    /// The check is **face-restricted** — a valid `hcomp` has `uᵢ i0 ≡ base` only
    /// *on* `φᵢ`, never globally — so it accepts a branch when the `i0`-cap is
    /// either globally def-eq to the floor (the ⊤-face / constant-on-cap case) or
    /// agrees with it on every disjunct of `φᵢ` (via [`Self::heads_agree_on_face`],
    /// the *same* face-restriction the overlap check uses). A ⊥ (inactive) branch
    /// imposes no constraint. A system Clean cannot parse adds nothing (the
    /// ordinary typing checks already ran), mirroring [`Self::validate_hcomp_system`].
    ///
    /// SOUNDNESS of the relaxation: both accepted cases imply `uᵢ i0 ≡ base` on
    /// `φᵢ` (global agreement is strictly stronger), so an accepted cap is genuine.
    /// `heads_agree_on_face` only substitutes interval atoms it can resolve to a
    /// free variable; a face it cannot restrict makes it return `false`, so the
    /// branch is rejected unless globally def-eq — conservative (never a false
    /// accept), never letting a floor-disagreeing branch through.
    pub(in crate::tc) fn validate_hcomp_cap(
        &self,
        phi: &Expr,
        u: &Expr,
        base: &Expr,
    ) -> Result<(), TypeError> {
        let (system, interner) = match self.parse_system_interned(phi, u, WhnfMode::Full) {
            Some(s) => s,
            None => return Ok(()),
        };
        let i0 = Expr::from_kind(ExprKind::CubicalI0);
        for (cof, ui) in &system {
            // A ⊥ branch is never active, so it imposes no cap constraint.
            if cof.is_bot() {
                continue;
            }
            // The cap is the tube's `i0`-end `uᵢ i0`, which must match the floor
            // on the face `φᵢ`.
            let cap = Expr::app(ui.clone(), i0.clone());
            // Global agreement (⊤ faces, tubes whose `i0`-cap is the floor
            // everywhere) ⇒ a fortiori agreement on the face.
            if self.is_def_eq(&cap, base) {
                continue;
            }
            // Otherwise require agreement on every disjunct of `φᵢ` (the exact
            // face-restriction `validate_hcomp_system` uses for the overlap check).
            if self.heads_agree_on_face(&cap, base, cof, &interner) {
                continue;
            }
            return Err(TypeError::TypeMismatch {
                expected: Box::new(base.clone()),
                inferred: Box::new(cap),
                location: None,
            });
        }
        Ok(())
    }

    /// Run the `hcomp` well-formedness side conditions (overlap agreement +
    /// cap/floor agreement) on behalf of the **certificate verifier**, which —
    /// unlike the release inference path — represents binder variables as loose
    /// de Bruijn `BVar`s relative to a verifier-supplied binder context
    /// (`binder_ctx`, outermost first) rather than as opened `FVar`s.
    ///
    /// SOUNDNESS: this is the exact same pair of checks
    /// ([`Self::validate_hcomp_system`] + [`Self::validate_hcomp_cap`]) the
    /// release fast path and the certificate *builder* run; the certificate
    /// *verifier* (`cert/verifier/cubical.rs`) previously omitted them, so it
    /// would re-verify a floor-disagreeing `hcomp` such as
    /// `hcomp {Nat} [(j=1)↦λ_.succ zero] zero` — whose `<j>` inhabits
    /// `Path Nat 0 1` — even though `infer_type` rejects it, violating the
    /// verifier's own `infer_type(expr) == result` contract. To run the
    /// FVar-based validators faithfully (so the face-restricted `heads_agree_on_face`
    /// can substitute the interval variables a well-formed cap depends on, rather
    /// than conservatively over-rejecting on un-openable loose `BVar` atoms), the
    /// verifier's binder context is mirrored into fresh `FVar`s and `phi`/`u`/`base`/`ty`
    /// are opened against them — exactly the locally-nameless form the release path
    /// already operates in (where `CubicalPathLam` inference opened the binder first).
    pub(crate) fn validate_hcomp_for_cert(
        &self,
        binder_ctx: &[Expr],
        phi: &Expr,
        u: &Expr,
        base: &Expr,
        ty: &Expr,
    ) -> Result<(), TypeError> {
        let save = self.ctx_len();
        // Push one fresh FVar per verifier binder (outermost first); each binder's
        // type is opened against the FVars already in scope (locally-nameless).
        let mut fvars: Vec<Expr> = Vec::with_capacity(binder_ctx.len());
        for binder_ty in binder_ctx {
            let mut rev = fvars.clone();
            rev.reverse();
            let opened_ty = binder_ty.instantiate_rev(&rev);
            let id = self.ctx_push(Name::anon(), opened_ty, BinderInfo::Default);
            fvars.push(Expr::fvar(id));
        }
        // `instantiate_rev` maps `BVar(0)` (innermost) to `rev[0]`; the innermost
        // binder is the *last* pushed FVar, so reverse the outermost-first vector.
        let mut rev = fvars.clone();
        rev.reverse();
        let phi_o = phi.instantiate_rev(&rev);
        let u_o = u.instantiate_rev(&rev);
        let base_o = base.instantiate_rev(&rev);
        let ty_o = ty.instantiate_rev(&rev);
        let result = self
            .validate_hcomp_system(&phi_o, &u_o, &ty_o)
            .and_then(|()| self.validate_hcomp_cap(&phi_o, &u_o, &base_o));
        self.ctx_truncate_to(save);
        result
    }

    /// Check that two `hcomp` tube heads `hi`, `hj` agree **on the overlap face**
    /// `overlap` (a `Cofib` in DNF). For each disjunct (a conjunction of atoms
    /// `var = endpoint`), substitute every atom's interval variable to its endpoint
    /// (`i0`/`i1`) in both heads and compare with [`Self::is_def_eq`]. Agreement
    /// holds iff the restricted heads are def-eq on *every* disjunct.
    ///
    /// SOUNDNESS: this only ever *accepts* a system; it substitutes the interval
    /// variables the overlap pins (looked up from the interner) and compares the
    /// resulting concrete restrictions. An atom whose interned interval term is not
    /// a free variable (so it cannot be substituted by `subst_fvar`) makes the
    /// check return `false` (conservative — the caller then rejects unless the
    /// heads are globally def-eq), never a spurious accept. Because the whnf
    /// `hcomp` rule only fires a branch on a *true* face, any assignment that makes
    /// two branches simultaneously total satisfies their overlap, where this check
    /// has verified the heads agree — so picking the first total branch stays
    /// canonical.
    pub(in crate::tc) fn heads_agree_on_face(
        &self,
        hi: &Expr,
        hj: &Expr,
        overlap: &Cofib,
        interner: &[Expr],
    ) -> bool {
        let i0 = Expr::from_kind(ExprKind::CubicalI0);
        let i1 = Expr::from_kind(ExprKind::CubicalI1);
        // ⊤ overlap (empty conjunct) ⇒ no restriction ⇒ must be globally def-eq,
        // which the caller already tested. Treat as "not verified here".
        let disjuncts = overlap.disjuncts();
        if disjuncts.is_empty() {
            return false; // ⊥ overlap is handled by the caller before calling us.
        }
        for conj in disjuncts {
            if conj.is_empty() {
                return false; // ⊤ disjunct: no substitution can be applied.
            }
            let mut ri = hi.clone();
            let mut rj = hj.clone();
            let mut substitutable = true;
            for atom in conj {
                let Some(ivar) = interner.get(atom.var() as usize) else {
                    substitutable = false;
                    break;
                };
                let ExprKind::FVar(id) = ivar.kind() else {
                    substitutable = false;
                    break;
                };
                let endpoint = if atom.value() { &i1 } else { &i0 };
                ri = ri.subst_fvar(*id, endpoint);
                rj = rj.subst_fvar(*id, endpoint);
            }
            if !substitutable || !self.is_def_eq(&ri, &rj) {
                return false;
            }
        }
        true
    }

    /// Parse a cofibration `Expr` with a fresh interner and full WHNF (test-only
    /// access to the otherwise-private parser, for the round-trip test).
    #[cfg(test)]
    pub(crate) fn parse_cofib_for_test(&self, e: &Expr) -> Option<Cofib> {
        let mut interner = Vec::new();
        self.parse_cofib(e, &mut interner, WhnfMode::Full)
    }

    /// Parse a system `(phi, u)` with full WHNF (test-only access).
    #[cfg(test)]
    pub(crate) fn parse_system_for_test(&self, phi: &Expr, u: &Expr) -> Option<Vec<(Cofib, Expr)>> {
        self.parse_system(phi, u, WhnfMode::Full)
    }

    /// Build the recursor-based field projection (the "predecessor") for the
    /// single self-recursive field of `target_ctor` in inductive `ind_name`
    /// (test-only access to [`Self::build_self_recursive_field_projection`]).
    #[cfg(test)]
    pub(crate) fn build_field_projection_for_test(
        &self,
        ind_name: &Name,
        target_ctor: &Name,
    ) -> Option<Expr> {
        let ind = self.env.get_inductive(ind_name)?;
        let rec_name = Name::append(ind_name, "rec");
        self.build_self_recursive_field_projection(ind, target_ctor, &rec_name)
    }

    /// Build the recursor-based projection `projᵢ : I → F` extracting the single
    /// **non-recursive** field of `target_ctor` (test-only access to
    /// [`Self::build_single_field_projection`]).
    #[cfg(test)]
    pub(crate) fn build_single_field_projection_for_test(
        &self,
        ind_name: &Name,
        target_ctor: &Name,
        field_ty: &Expr,
        field_level: &Level,
    ) -> Option<Expr> {
        let ind = self.env.get_inductive(ind_name)?;
        let rec_name = Name::append(ind_name, "rec");
        self.build_single_field_projection(ind, target_ctor, &rec_name, field_ty, field_level)
    }

    /// Parse a Glue system `sys` with full WHNF (test-only access).
    #[cfg(test)]
    pub(crate) fn parse_glue_system_for_test(
        &self,
        sys: &Expr,
    ) -> Option<Vec<(Cofib, Expr, Expr)>> {
        self.parse_glue_system(sys, WhnfMode::Full)
    }

    /// Attempt one head-reduction step for `CubicalTransp { ty, phi, base }`.
    ///
    /// `transp` is `coe^{i0→i1}`: `transp A φ base` and `coe A i0 i1 base` have
    /// the same typing (`base : A i0`, result `A i1`) and the same intended
    /// meaning (φ is the constancy cofibration, which the sound coe rules do not
    /// rely on). We delegate to [`try_coe_reduction`] and only rewrite when coe
    /// actually makes progress — otherwise `transp` stays stuck (as-is).
    pub(in crate::tc) fn try_transp_reduction(&self, e: &Expr, _mode: WhnfMode) -> Option<Expr> {
        let ExprKind::CubicalTransp { ty, base, .. } = e.kind() else {
            return None;
        };
        // `transp ty φ base` is definitionally `coe^{i0→i1} ty base` — it ignores
        // the constancy cofibration `φ` (which `infer_cubical_transp` does not
        // currently enforce anyway). Always rewrite transport to the canonical
        // `coe` form so a *stuck* transport has a single normal form (`coe`, not a
        // distinct `transp` head); coe then reduces further or stays stuck. This
        // is a type-preserving rewrite (both have type `ty i1`), and it terminates
        // (a `transp` head becomes a `coe` head exactly once — coe never rewrites
        // back to transp).
        Some(Expr::from_kind(ExprKind::CubicalCoe {
            ty: ty.clone(),
            r: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
            s: Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
            base: base.clone(),
        }))
    }

    /// Attempt one head-reduction step for `CubicalCoe { ty, r, s, base }`.
    ///
    /// Returns `Some(reduced)` when a coercion rule fires, or `None` to leave the
    /// term stuck (the WHNF trampoline then reports `Done`).
    ///
    /// Implemented rules (all type-preserving — see module note):
    /// * **Degenerate** `r ≡ s`  ⇒  `base`.
    /// * **Constant line** (`λ i. A` with `A` independent of `i`)  ⇒  `base`.
    /// * **Pi** `λ i. Π(x:B[i]). C[i,x]`  ⇒  the standard Pi-coe lambda (with the
    ///   backward coercion on the argument and the fill inside the codomain line).
    /// * **Sigma** `λ i. Σ(x:A[i]). B[i,x]` on a literal `Sigma.mk` base ⇒ the
    ///   CCHM Σ rule (`coe` the fst, `coe` the snd along the coe-filler line); see
    ///   [`Self::try_coe_sigma`].
    /// * **(non-dependent) Path** `λ i. Path (A[i]) (u[i]) (v[i])` ⇒ the CCHM comp
    ///   `<j> comp (λ i. A i) [(j=0)↦u,(j=1)↦v] (p@j)`; see [`Self::try_coe_path`].
    /// * **Glue** at the transport endpoints ⇒ the `transp`-over-Glue rule.
    ///
    /// Left stuck (sound): **dependent `PathP`** (its system tubes are only
    /// well-typed on their faces, which the total `System.cons` tube typing cannot
    /// express), **residual Glue**, **Sort/Nat/neutral heads** (covered by the
    /// constant rule when applicable, else stuck).
    pub(in crate::tc) fn try_coe_reduction(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        let ExprKind::CubicalCoe { ty, r, s, base } = e.kind() else {
            return None;
        };

        // Rule 1 — degenerate `r ≡ s`: `coe A r r base ↝ base`.
        // Type-safe because `A r ≡ A s`, so `base : A r` already has type `A s`.
        if self.is_def_eq(r, s) {
            return Some(base.as_ref().clone());
        }

        // Expose the line's binder structure (unfold a neutral/defined head).
        let line = self.whnf_recurse(ty, mode);
        if let ExprKind::Lam(_, _dom, body) = line.kind() {
            // Rule 2 — constant family: the line is the same type at every
            // interval point, so `A r ≡ A s` and coercion is the identity.
            if self.coe_line_body_is_constant(body, mode) {
                return Some(base.as_ref().clone());
            }
            // Rule 3 — interval-dependent Pi line.
            if let Some(reduced) = self.try_coe_pi(&line, r, s, base, mode) {
                return Some(reduced);
            }
            // Rule 3.5 — *deep* constant family: the line is degenerate up to
            // definitional equality even though the cheap syntactic check (Rule 2)
            // could not see it through a neutral head's arguments or under a
            // path-lambda. This is what makes the `J` β-rule compute — the motive
            // line `λ i. P (p@i) (<j> p@(I.min i j))` collapses to `λ i. P a (<j> a)`
            // when `p = refl a`. Placed after the Pi rule so Pi lines keep their
            // standard reduction, and before the `ua` rule (which the check
            // correctly declines for the univalence line — see the method note).
            if self.coe_line_constant_deep(body, mode) {
                return Some(base.as_ref().clone());
            }
            // Rule 4 — interval-dependent **Σ** line (`coe`-over-Sigma): the CCHM
            // comp-by-type-former rule for the dependent pair. Fires only on a
            // literal `Sigma.mk` base with a `Sigma`-headed line (placed after the
            // constant rules so a degenerate Σ line short-circuits to `base`).
            if let Some(reduced) = self.try_coe_sigma(&line, r, s, base, mode) {
                return Some(reduced);
            }
            // Rule 5 — interval-dependent **Path** line (`coe`-over-Path): the CCHM
            // comp for the (non-dependent) path type, assembled from `hcomp`+`coe`
            // (= `comp`) and the interval connections. The *dependent* `PathP` form
            // is left stuck (its system tubes are only well-typed on their faces,
            // which the total `System.cons` tube typing cannot express).
            if let Some(reduced) = self.try_coe_path(&line, r, s, base, mode) {
                return Some(reduced);
            }
            // Rule 6 — the general CCHM **`transp`-over-`Glue`** computation rule at
            // the transport endpoints (`coe (λ i. Glue (A i) [φᵢ↦(Tᵢ,eᵢ)]) i0 i1 b`).
            // Subsumes the `ua`-specialized rule (`coe (ua e) i0 i1 x ↝ e.fwd x`).
            // Fires only when some cell face is `⊤` at `i1` (the result type
            // degenerates to that cell); a Glue line with a *residual* (neutral) Glue
            // at `i1`, or non-transport endpoints, stays stuck.
            if let Some(reduced) = self.try_coe_glue_compute(body, r, s, base, mode) {
                return Some(reduced);
            }
            // Dependent PathP / general (residual) Glue / other former: stuck.
        }

        None
    }

    /// The general CCHM **`transp`-over-`Glue`** computation rule at the transport
    /// endpoints — the `coe` over a `Glue` line that makes `winding(loop²) ↝ ofNat 2`
    /// (and, as the special case `ua`, `transport (ua e) x ↝ Equiv.fwd e x`):
    ///
    /// ```text
    /// coe (λ i. Glue (A i) φ [ φₖ(i) ↦ (Tₖ i, eₖ i) ]) i0 i1 base
    ///   ↝  Equiv.bwd (eₖ i1) (coe (λ i. A i) i0 i1 (unglue@i0 base))
    ///        — when some cell face φₖ ⇓ ⊤ at i1 (so G(i1) degenerates to Tₖ(i1)).
    /// ```
    ///
    /// `body` is the line body under its interval binder (de Bruijn `BVar 0`). The
    /// real work — extracting the base line, parsing the system, locating the
    /// `i1`-total cell, and assembling the reduct — is in [`Self::coe_glue_line`],
    /// which also documents *where the CCHM correction `hcomp` is* and *why this is
    /// not the unsound `substComposite` shortcut*.
    ///
    /// ## Precision (why it cannot over-fire)
    ///
    /// Returns `None` (stuck, sound) unless: the endpoints are the **transport**
    /// endpoints `r ⇓ i0`, `s ⇓ i1`; the opened line WHNFs to `Glue (A i) φ sys`
    /// (reserved `Glue` head, 3 args); the system parses; **some** cell is `⊤` at
    /// `i1`; and the assembled reduct mentions no dangling interval variable. A line
    /// with only `⊥`/neutral cells at `i1` (a residual Glue at `i1`), or non-transport
    /// endpoints, stays stuck — the genuinely-general (non-vacuous-correction) case is
    /// intentionally not handled.
    fn try_coe_glue_compute(
        &self,
        body: &Expr,
        r: &Expr,
        s: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        // Cubical-only — mirrors the gating of `try_glue_reduction` in `whnf.rs`.
        if !self.mode.has_cubical_layer() {
            return None;
        }
        // Endpoints must be the canonical transport endpoints in EITHER orientation:
        // the **forward** `(r,s) ⇓ (i0,i1)` (the existing winding direction) or the
        // **backward** `(r,s) ⇓ (i1,i0)` (the new `decode`/`pred` direction). Resolve
        // each to a definite endpoint; both must be definite and opposite. A line with
        // a non-endpoint (neutral `r`/`s`) stays stuck.
        let endpoint = |e: &Expr| match self.whnf_recurse(e, mode).kind() {
            ExprKind::CubicalI0 => Some(false),
            ExprKind::CubicalI1 => Some(true),
            _ => None,
        };
        let r_is_one = endpoint(r)?;
        let s_is_one = endpoint(s)?;
        if r_is_one == s_is_one {
            return None; // `r ≡ s` is handled earlier; equal definite endpoints can't occur here.
        }
        let mk = |is_one: bool| {
            if is_one {
                Expr::from_kind(ExprKind::CubicalI1)
            } else {
                Expr::from_kind(ExprKind::CubicalI0)
            }
        };
        let r_end = mk(r_is_one);
        let s_end = mk(s_is_one);
        let save_len = self.ctx_len();
        let iv = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        let result = self.coe_glue_line(body, iv, &r_end, &s_end, base, mode);
        self.ctx_truncate_to(save_len);
        result
    }

    /// Build the CCHM `transp`-over-`Glue` reduct for the opened line `body` (under
    /// the fresh interval binder `iv`), transporting `base : G(r)` to `G(s)`, where
    /// `(r,s)` (= `r_end`/`s_end`) are the **transport endpoints** in either
    /// orientation: forward `(i0,i1)` (the winding/`succ` direction) or backward
    /// `(i1,i0)` (the `decode`/`pred` direction). The rule is fully symmetric — the
    /// only thing that matters is the *target* endpoint `s`.
    ///
    /// `G(i) = Glue (A i) φ [ φₖ(i) ↦ (Tₖ i, eₖ i) ]`. This implements the CCHM
    /// composition for `Glue` in the **result-degenerate** case — i.e. when some
    /// cell face is `⊤` at the **target** `s`, so `G(s)` reduces to that cell's type
    /// `Tₖ(s)`:
    ///
    /// ```text
    ///   a₀  := unglue (A r) (φ@r) (sys@r) base   : A(r)   -- underlying base (at source)
    ///   a₁  := coe (λ i. A i) r s a₀             : A(s)   -- coerce the base line r→s
    ///   t₁  := Equiv.bwd (eₖ s) a₁               : Tₖ(s)  -- fiber-center point (at target)
    ///   ↝ t₁
    /// ```
    ///
    /// ## Where the CCHM correction is, and why this is NOT the unsound shortcut
    ///
    /// The full CCHM reduct is `glue [φₖ(s) ↦ t₁] a₁`, where `a₁` is a **correction
    /// `hcomp`** over `A(s)` that makes the underlying element agree with `eₖ.fwd t₁`
    /// on `φₖ(s)`. Here `φₖ(s) ⇓ ⊤`, so the `Glue` **degenerates** to `Tₖ(s)` and
    /// `glue [⊤ ↦ t₁] a₁ ↝ t₁` (the glue boundary discards its base component `a₁`).
    /// Hence the correction acts only on the discarded component and the reduct is
    /// exactly the fiber-center **point** `t₁`. This is the genuine transp-over-Glue
    /// value (`t₁ = g(a₁)`, the point of the contractible-fiber centre of `eₖ` over
    /// `a₁`), obtained from the equivalence's **backward map** `Equiv.bwd` — the
    /// *computable* form of the fiber centre carried by every `Equiv.mk`. It is NOT
    /// the forbidden `transport (p∙q) ≡ transport q ∘ transport p` shortcut: it never
    /// equates the transport to a wrong value, and the correction is provably vacuous
    /// here (it only changes the base that the `⊤`-degeneration drops).
    ///
    /// ## Subsumes the `ua` rule, both directions (and stays stuck exactly where it must)
    ///
    /// For the `ua` line `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, idEquiv B)]`:
    /// * **forward** `(r,s)=(i0,i1)`: the `s`-total cell is `(i=1)` with `idEquiv`,
    ///   the base line `λ i. B` is constant, `a₀ = unglue@i0 x = e.fwd x`, `a₁ = a₀`,
    ///   `t₁ = Equiv.bwd (idEquiv B) a₁ = a₁`, so `coe (ua e) i0 i1 x ↝ e.fwd x`;
    /// * **backward** `(r,s)=(i1,i0)`: the `s`-total cell is `(i=0)` with `e`,
    ///   `a₀ = unglue@i1 x = idEquiv.fwd x = x`, `a₁ = x`, `t₁ = Equiv.bwd e x = e.bwd x`,
    ///   so `coe (ua e) i1 i0 x ↝ e.bwd x` (the *inverse* transport — `pred` for `ua sucEquiv`).
    ///
    /// A line whose cells are all `⊥`/neutral at the target `s` (a *residual* Glue at
    /// `s`) has no `⊤` cell there, so the rule returns `None` and stays stuck — that
    /// genuinely-general case (a non-vacuous correction over a residual Glue) is
    /// intentionally not handled, in either orientation.
    ///
    /// ## Type preservation (the soundness anchor)
    ///
    /// On `φₖ(s) ⇓ ⊤`, `G(s) ≡ Tₖ(s)` (the `Glue`-type boundary picks the *first*
    /// total cell — the same `k` chosen here). `eₖ(s) : Equiv (Tₖ s) (A s)`, so
    /// `Equiv.bwd (eₖ s) : A(s) → Tₖ(s)` and `a₁ : A(s)` give `t₁ : Tₖ(s) ≡ G(s)` —
    /// the rewrite preserves type in either orientation. A line that does not WHNF to
    /// `Glue …`, or a system Clean cannot parse, stays stuck (`None`), which is sound.
    fn coe_glue_line(
        &self,
        body: &Expr,
        iv: FVarId,
        r_end: &Expr,
        s_end: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        // Expose the per-point type `Glue (A i) φ sys` and extract the base line `A i`,
        // the overall extent `φ`, the system `sys`, and the universe level.
        //
        // The `is_def_eq` phases that drive
        // `coe` reduction run in **no-delta** WHNF modes (`NoDeltaCheapProj`/
        // `NoDeltaFullProj`); a Glue line written through a *reducible definition*
        // (e.g. `helix := S¹.rec … (ua e)`, so the line is `λ i. helix (loop@i)`) needs
        // DELTA to unfold that head to the `Glue` former, which the no-delta mode will
        // not do — leaving the whole `coe` stuck. We therefore expose the former with
        // FULL transparency. SOUNDNESS: WHNF is meaning-preserving, so a stronger
        // reduction can only expose the genuine per-point type former, never a
        // different one; the reduct built below is the same type-preserving CCHM value.
        let opened = self.open_bvar(body, iv);
        let p = self.whnf_recurse(&opened, WhnfMode::Full);
        let ExprKind::Const(name, levels) = p.get_app_fn().kind() else {
            return None;
        };
        if *name != *glue_names::GLUE {
            return None;
        }
        let args = p.get_app_args();
        if args.len() != 3 {
            return None;
        }
        let level = levels.first()?.clone();
        let a_base = args[0].clone(); // A(iv)  — mentions iv
        let phi_overall = args[1].clone(); // φ     — mentions iv
        let sys = args[2].clone(); // system — mentions iv

        // Parse the system cells `[(faceₖ, Tₖ, eₖ, ieₖ)]` (each still mentioning iv).
        let mut cells: Vec<(Expr, Expr, Expr, Expr)> = Vec::new();
        let mut cur = sys.clone();
        loop {
            let w = self.whnf_recurse(&cur, mode);
            if let Some((_b, phi_k, t_k, e_k, ie_k, tail)) = self.match_glue_cons(&w) {
                cells.push((phi_k, t_k, e_k, ie_k));
                cur = tail;
                continue;
            }
            let ExprKind::Const(nil_name, _) = w.get_app_fn().kind() else {
                return None;
            };
            if *nil_name == *glue_names::GLUE_SYS_NIL {
                break;
            }
            return None;
        }
        if cells.is_empty() {
            return None;
        }

        // Find the FIRST cell whose face is `⊤` at the **target** `s` — the cell `G(s)`
        // degenerates to (the same cell the `Glue`-type boundary rule would pick). No
        // such cell ⇒ a residual Glue at `s` ⇒ stuck (sound; the general correction is
        // not done). Works for either orientation: `s = i1` (forward) or `s = i0`
        // (backward).
        let mut k = None;
        for (idx, (phi_k, _t_k, _e_k, _ie_k)) in cells.iter().enumerate() {
            let phi_at_s = phi_k.subst_fvar(iv, s_end);
            let mut interner: Vec<Expr> = Vec::new();
            let cof = self.parse_cofib(&phi_at_s, &mut interner, mode)?;
            if cof.is_top() {
                k = Some(idx);
                break;
            }
        }

        // a₀ = unglue (A@r) (φ@r) (sys@r) base   — the underlying base in A(r) (the
        // *source* endpoint). Reduces via the unglue total-face rule (the system has a
        // `⊤` cell at `r` whenever the line is a genuine transport line — the `ua`
        // boundary has `⊤` cells at *both* endpoints; if not, a₀ stays stuck and the
        // whole reduct stays stuck-but-sound). Shared by the ⊤-cell and residual
        // branches.
        let a0 = Expr::apps(
            Expr::const_(glue_names::UNGLUE.clone(), vec![level.clone()]),
            [
                a_base.subst_fvar(iv, r_end),
                phi_overall.subst_fvar(iv, r_end),
                sys.subst_fvar(iv, r_end),
                base.clone(),
            ],
        );

        // a₁ = coe (λ i. A i) r s a₀   — coerce the base along the Glue base line, in
        // the SAME orientation as the outer coe.
        let a_line = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::CubicalInterval),
            a_base.abstract_fvar(iv),
        );
        let a1 = Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(a_line),
            r: Arc::new(r_end.clone()),
            s: Arc::new(s_end.clone()),
            base: Arc::new(a0),
        });

        let result = match k {
            // ── ⊤-cell (result-degenerate) case ───────────────────────────────────
            // Some cell is `⊤` at the target `s`, so `G(s) ≡ Tₖ(s)` and the reduct is
            // the fibre-centre POINT `t₁ = Equiv.bwd (eₖ s) a₁` (the glue boundary
            // discards the underlying component — see the method note). This is the
            // existing, value-correct `winding`/`ua` rule, unchanged.
            Some(k) => {
                let (_phi_k, t_k, e_k, _ie_k) = &cells[k];
                Expr::apps(
                    Expr::const_(glue_names::EQUIV_BWD.clone(), vec![level.clone()]),
                    [
                        t_k.subst_fvar(iv, s_end),
                        a_base.subst_fvar(iv, s_end),
                        e_k.subst_fvar(iv, s_end),
                        a1,
                    ],
                )
            }
            // ── residual (no ⊤ cell at `s`) case ──────────────────────────────────
            // `G(s)` is a genuine Glue with a neutral face — the CCHM `comp^i(Glue)`
            // that reads the cell's carried `isEquiv` to synthesise the glued partial
            // element + correction `hcomp`. Fires only on a single computing-witness
            // cell; everything else stays soundly stuck (`None`).
            None => self.coe_glue_residual(&cells, iv, s_end, &a_base, &a1, &level, mode)?,
        };

        // The reduct must not mention the interval binder `iv` (everything was either
        // substituted to `i0`/`i1` or abstracted into `a_line`); guard defensively so
        // no dangling variable escapes once the binder context is truncated.
        if result.abstract_fvar(iv).has_loose_bvar(0) {
            return None;
        }
        Some(result)
    }

    /// The **residual** CCHM `comp^i(Glue)` reduct — the case the previous sessions
    /// left stuck because the cell carried no `isEquiv`. With the carried
    /// contractible-fibre witness ([`register_glue_axioms`]'s `Glue.Sys.cons` `ie`
    /// field), this now computes for a *single-cell* Glue line whose cell carries a
    /// **computing** witness (`coeEquiv`/`idEquiv` cells — the `hcomp`-in-universe
    /// case); an opaque cell (`Equiv.toIsEquiv`, the `ua` cells) leaves the fibre
    /// centre stuck and the whole rule stays `None` (sound — never a wrong value).
    ///
    /// `cells` are the parsed cells `[(φ, T, e, ie)]` (each mentioning `iv`), `a1`
    /// the already-built coerced underlying base `coe (λi.A i) r s (unglue@r base) :
    /// A(s)`, and `a_base = A(iv)`. The reduct is, with everything taken at `s`:
    ///
    /// ```text
    ///   ie(s) a₁ : isContr (fiber (Equiv.fwd e(s)) a₁)
    ///   (x₁, p) := ((ie(s) a₁).fst).{fst,snd}            -- the fibre centre
    ///             x₁ : T(s),  p : Path A(s) (e(s).fwd x₁) a₁
    ///   a₁'' := hcomp {A(s)} [ ψ(s) ↦ λ j. p @ (~j) ] a₁  -- the correction hcomp
    ///   ↝ glue A(s) T(s) ψ(s) e(s) ie(s) x₁ a₁''   : Glue A(s) ψ(s) [ψ(s)↦(T(s),e(s),ie(s))]
    /// ```
    ///
    /// ## Value-correctness (the Glue laws are the oracle)
    ///
    /// * **unglue-β:** `unglue (result) ↝ a₁''` — the result is a genuine glued
    ///   element whose underlying part is the correction composite.
    /// * **Glue boundary:** on `ψ(s) ⊤` the glue well-formedness holds because the
    ///   correction makes `a₁'' ≡ e(s).fwd x₁` there: `a₁''|_{ψ⊤} = (λj.p@~j) i1 =
    ///   p@i0 = e(s).fwd x₁` (the path's *left* endpoint).
    /// * **cap coherence:** the correction `hcomp`'s wall at `j = i0` is
    ///   `p @ (~i0) = p @ i1 = a₁` (the path's *right* endpoint, since
    ///   `p : Path … (e(s).fwd x₁) a₁`), which is exactly the floor — so
    ///   `validate_hcomp_cap` accepts.
    /// * **agreement with the quasi-inverse where that is correct:** for `coeEquiv`
    ///   cells the centre `x₁` is `Equiv.bwd (e(s)) a₁` (the coe-backward, the genuine
    ///   coherent inverse), so on the `⊤`-cell degeneration the residual rule and the
    ///   existing `Equiv.bwd` rule produce the same value (subsumption).
    /// * the centre is read from the *computing* `is_equiv_coe`/`id_is_equiv` witness
    ///   (not the quasi-inverse shortcut), so it is the genuine contractible-fibre
    ///   point — the rule only fires when that genuinely reduces to a literal pair.
    ///
    /// SOUNDNESS: type-preserving (`result : Glue A(s) ψ(s) [ψ(s)↦cell] ≡ G(s)` for a
    /// single hcomp-universe cell, where the Glue extent equals the cell face) and
    /// it only fires when the fibre centre concretely computes — exactly the cells
    /// whose witness is coherent.
    #[allow(clippy::too_many_arguments)]
    fn coe_glue_residual(
        &self,
        cells: &[(Expr, Expr, Expr, Expr)],
        iv: FVarId,
        s_end: &Expr,
        a_base: &Expr,
        a1: &Expr,
        level: &Level,
        _mode: WhnfMode,
    ) -> Option<Expr> {
        // Single-cell residual scope: the `glue` intro encodes exactly one cell whose
        // face is the Glue extent, so a multi-cell residual Glue is left stuck (sound).
        if cells.len() != 1 {
            return None;
        }
        let (phi_k, t_k, e_k, ie_k) = &cells[0];
        let a_s = a_base.subst_fvar(iv, s_end); // A(s)
        let phi_s = phi_k.subst_fvar(iv, s_end); // ψ(s)  (neutral here)
        let t_s = t_k.subst_fvar(iv, s_end); // T(s)
        let e_s = e_k.subst_fvar(iv, s_end); // e(s) : Equiv T(s) A(s)
        let ie_s = ie_k.subst_fvar(iv, s_end); // ie(s) : isEquiv (Equiv.fwd e(s))

        // Fibre centre of `Equiv.fwd e(s)` over a₁. `Full` WHNF (meaning-preserving)
        // drives the `coe`-over-Pi/Sigma chain inside `is_equiv_coe` so the centre
        // computes; an opaque `Equiv.toIsEquiv` witness stays a neutral spine ⇒ the
        // `match_sigma_mk` below returns `None` ⇒ the rule stays soundly stuck.
        let is_contr = self.whnf_recurse(&Expr::app(ie_s.clone(), a1.clone()), WhnfMode::Full);
        let (_ffib, _bcontr, centre, _contr) = self.match_sigma_mk(&is_contr)?;
        let fib = self.whnf_recurse(&centre, WhnfMode::Full);
        let (_t_dom, _bfam, x1, pth) = self.match_sigma_mk(&fib)?;

        // Correction hcomp  a₁'' = hcomp {A(s)} [ ψ(s) ↦ λ j. p @ (~j) ] a₁.
        let interval = || Expr::from_kind(ExprKind::CubicalInterval);
        let i_neg = |x: Expr| Expr::app(Expr::const_(conn_names::I_NEG.clone(), vec![]), x);
        // wall = λ j:I. p @ (~j).   `p` is closed in `iv`; lift by one under `λ j`.
        let wall = Expr::lam(
            BinderInfo::Default,
            interval(),
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(pth.lift(1)),
                arg: Arc::new(i_neg(Expr::bvar(0))),
            }),
        );
        let sys_nil = Expr::app(
            Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
            a_s.clone(),
        );
        let system = Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
            [a_s.clone(), phi_s.clone(), wall, sys_nil],
        );
        let a1pp = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(a_s.clone()),
            phi: Arc::new(phi_s.clone()),
            u: Arc::new(system),
            base: Arc::new(a1.clone()),
        });

        // result = glue A(s) T(s) ψ(s) e(s) ie(s) x₁ a₁''.
        Some(Expr::apps(
            Expr::const_(glue_names::GLUE_INTRO.clone(), vec![level.clone()]),
            [a_s, t_s, phi_s, e_s, ie_s, x1, a1pp],
        ))
    }

    /// Destructure a literal `Sigma.mk A B fst snd` (already WHNF'd) into its four
    /// owned arguments `(A, B, fst, snd)`. `None` for any other head/arity (so a
    /// *neutral* Σ point leaves the residual rule soundly stuck).
    fn match_sigma_mk(&self, e: &Expr) -> Option<(Expr, Expr, Expr, Expr)> {
        let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
            return None;
        };
        if *name != *sigma_names::SIGMA_MK {
            return None;
        }
        let args = e.get_app_args();
        if args.len() != 4 {
            return None;
        }
        Some((
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
            args[3].clone(),
        ))
    }

    /// Destructure a `Glue.Sys.cons B φ T e ie tail` cell (already WHNF'd) into its
    /// six owned arguments `(B, φ, T, e, ie, tail)`. `None` for any other head/arity.
    /// `ie : isEquiv (Equiv.fwd e)` is the carried contractible-fibre witness the
    /// residual `coe`-over-`Glue` rule reads to obtain the fibre centre at `s`.
    #[allow(clippy::type_complexity)]
    fn match_glue_cons(&self, e: &Expr) -> Option<(Expr, Expr, Expr, Expr, Expr, Expr)> {
        let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
            return None;
        };
        if *name != *glue_names::GLUE_SYS_CONS {
            return None;
        }
        let args = e.get_app_args();
        if args.len() != 6 {
            return None;
        }
        Some((
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
            args[3].clone(),
            args[4].clone(),
            args[5].clone(),
        ))
    }

    /// Coercion in a Pi type `λ i. Π(x:B[i]). C[i,x]`:
    ///
    /// ```text
    /// coe (λ i. Π(x:B). C) r s f
    ///   ↝ λ (x : B[s]).
    ///       coe (λ i. C[i, coe (λ j. B) s i x]) r s (f (coe (λ j. B) s r x))
    /// ```
    ///
    /// Soundness: this is the standard definitional Pi-coercion rule of Cartesian
    /// cubical type theory, a type-preserving rewrite. With
    /// `f : (λ i. Π(x:B).C) r = Π(x:B[r]). C[r,x]` and `x : B[s]`:
    /// * the **backward** `coe (λ j. B) s r x : B[r]` makes `f (…) : C[r, x_r]`,
    /// * the codomain line `λ i. C[i, coe (λ j. B) s i x]` connects `C[r, x_r]` at
    ///   `i=r` to `C[s, x]` at `i=s` (the fill `coe (λ j. B) s s x ≡ x` by the
    ///   degenerate rule), so the outer `coe … r s` lands in `C[s, x]`,
    /// * giving the whole lambda type `Π(x:B[s]). C[s,x] = (λ i. Π(x:B).C) s`.
    ///
    /// `line` is the already-WHNF'd line `λ i. P[i]`. Returns `None` when `P` is
    /// not a Pi.
    fn try_coe_pi(
        &self,
        line: &Expr,
        r: &Expr,
        s: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        let ExprKind::Lam(_, _dom_i, p_body) = line.kind() else {
            return None;
        };

        let save_len = self.ctx_len();
        let iv = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        // Expose the per-point type `P[iv] = Π(x:B[iv]). C[iv,x]`.
        let p_open = self.whnf_recurse(&self.open_bvar(p_body, iv), mode);

        let result = if let ExprKind::Pi(bi_x, b_dom, c_cod) = p_open.kind() {
            let bi_x = *bi_x;
            // The domain line `λ j. B[j]` (re-abstract the interval variable).
            let b_line = Expr::lam(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::CubicalInterval),
                b_dom.abstract_fvar(iv),
            );
            // The new binder domain `B[s]`.
            let b_s = b_dom.subst_fvar(iv, s);

            // Open the value binder with a fresh `x : B[s]`.
            let xv = self.ctx_push(Name::anon(), b_s.clone(), bi_x);

            // Backward coercion on the argument: `coe (λ j. B) s r x : B[r]`.
            let arg_coe = Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(b_line.clone()),
                r: Arc::new(s.clone()),
                s: Arc::new(r.clone()),
                base: Arc::new(Expr::fvar(xv)),
            });
            // `f (coe (λ j. B) s r x) : C[r, x_r]`.
            let f_applied = Expr::app(base.clone(), arg_coe);

            // Codomain line `λ i. C[i, coe (λ j. B) s i x]`.
            let jv = self.ctx_push(
                Name::anon(),
                Expr::from_kind(ExprKind::CubicalInterval),
                BinderInfo::Default,
            );
            // The fill `coe (λ j. B) s i x : B[i]` (here `i = jv`).
            let fill = Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(b_line.clone()),
                r: Arc::new(s.clone()),
                s: Arc::new(Expr::fvar(jv)),
                base: Arc::new(Expr::fvar(xv)),
            });
            // `C[iv, fill]` — instantiate the Pi value binder (BVar 0 = x).
            let c_at = c_cod.instantiate(&fill);
            // `C[jv, fill]` — relocate the interval point iv → jv.
            let c_at_j = c_at.subst_fvar(iv, &Expr::fvar(jv));
            // `λ i. C[i, …]` (re-abstract the interval variable jv).
            let c_line = Expr::lam(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::CubicalInterval),
                c_at_j.abstract_fvar(jv),
            );

            // Outer coercion over the codomain line: `coe (λ i. C[…]) r s f_applied`.
            let inner_coe = Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(c_line),
                r: Arc::new(r.clone()),
                s: Arc::new(s.clone()),
                base: Arc::new(f_applied),
            });
            // Outer `λ (x:B[s]). <inner_coe>` — `abstract_fvar` is depth-aware
            // across the nested interval lam inside `c_line`.
            Some(Expr::lam(bi_x, b_s, inner_coe.abstract_fvar(xv)))
        } else {
            None
        };

        self.ctx_truncate_to(save_len);
        result
    }

    /// Coercion over a **dependent-sum (`Σ`) line** `λ i. Σ (x:A i). B i x` — the
    /// CCHM comp-by-type-former rule for the dependent pair:
    ///
    /// ```text
    /// coe (λ i. Σ (x:A i). B i x) r s (Sigma.mk A' B' a b)
    ///   ↝ Sigma.mk (A s) (B s) a' b'
    ///   where a'      := coe (λ i. A i) r s a                    -- coerce the fst
    ///         fillA i := coe (λ i. A i) r i a                    -- the coe-filler of a
    ///         b'      := coe (λ i. B i (fillA i)) r s b          -- coerce the snd
    /// ```
    ///
    /// Fires only on a literal `Sigma.mk` base with a `Sigma`-headed line (both the
    /// non-dependent and the dependent `B`). A neutral base, a non-`Sigma` line, or
    /// the wrong arity stays **stuck** (`None`, sound).
    ///
    /// ## SOUNDNESS — type preservation (the standard Cartesian-cubical Σ rule)
    ///
    /// With `a : A r`, `b : B r a`:
    /// * `a' = coe (λ i. A i) r s a : A s`;
    /// * the second-component line `λ i. B i (fillA i)` connects `B r (fillA r)` to
    ///   `B s (fillA s)`; the coe-filler degenerates at its source —
    ///   `fillA r = coe (λ i. A i) r r a ≡ a` — so the line at `r` is `B r a` (the
    ///   type of `b`), and `fillA s = a'`, so the line at `s` is `B s a'`. Hence
    ///   `b' = coe (λ i. B i (fillA i)) r s b : B s a'`;
    /// * `Sigma.mk (A s) (B s) a' b' : Σ (A s) (B s)`, which is the original line at
    ///   `s`. So the rewrite is type-preserving. The *value* is checked by the
    ///   conformance tests (constant-line ⇒ id; fst/snd projection agreement).
    ///
    /// `line` is the already-WHNF'd coercion line `λ i. P[i]`.
    fn try_coe_sigma(
        &self,
        line: &Expr,
        r: &Expr,
        s: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        // Cubical-only (mirrors the gating of `try_coe_glue_compute`).
        if !self.mode.has_cubical_layer() {
            return None;
        }
        let ExprKind::Lam(_, _dom_i, p_body) = line.kind() else {
            return None;
        };
        // The base must WHNF to a literal `Sigma.mk A' B' a b` (4 args).
        let base_w = self.whnf_recurse(base, mode);
        let ExprKind::Const(mk_name, _) = base_w.get_app_fn().kind() else {
            return None;
        };
        if *mk_name != *sigma_names::SIGMA_MK {
            return None;
        }
        let mk_args = base_w.get_app_args();
        if mk_args.len() != 4 {
            return None;
        }

        let save_len = self.ctx_len();
        let iv = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        // Expose the per-point type `Σ (A iv) (B iv)`.
        let p_open = self.whnf_recurse(&self.open_bvar(p_body, iv), mode);
        let result = self.coe_sigma_line(&p_open, iv, r, s, mk_args[2], mk_args[3]);
        self.ctx_truncate_to(save_len);
        result
    }

    /// Assemble the `coe`-over-Sigma reduct for the opened per-point type
    /// `p_open = Σ (A iv) (B iv)` (under the fresh interval binder `iv`), coercing
    /// the literal pair components `a_field`/`b_field` from `r` to `s`. Returns
    /// `None` (⇒ caller stays stuck, sound) if `p_open` is not a `Sigma` head.
    ///
    /// The coe-filler `fillA i = coe (λ i. A i) r i a` is built with `iv` itself as
    /// the (variable) target endpoint, then `abstract_fvar(iv)` closes it under the
    /// second-component line's binder — so `fillA` is the genuine filler with
    /// `fillA r ≡ a`, `fillA s ≡ a'`.
    fn coe_sigma_line(
        &self,
        p_open: &Expr,
        iv: FVarId,
        r: &Expr,
        s: &Expr,
        a_field: &Expr,
        b_field: &Expr,
    ) -> Option<Expr> {
        let ExprKind::Const(sig_name, levels) = p_open.get_app_fn().kind() else {
            return None;
        };
        if *sig_name != *sigma_names::SIGMA {
            return None;
        }
        let sargs = p_open.get_app_args();
        if sargs.len() != 2 {
            return None;
        }
        let level = levels.first()?.clone();
        let a_iv = sargs[0].clone(); // A iv         (mentions iv)
        let b_iv = sargs[1].clone(); // B iv : A iv → Sort u  (mentions iv)

        let interval = || Expr::from_kind(ExprKind::CubicalInterval);
        let coe = |ty: Expr, rr: Expr, ss: Expr, b: Expr| {
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(ty),
                r: Arc::new(rr),
                s: Arc::new(ss),
                base: Arc::new(b),
            })
        };

        // A_line = λ i. A i.
        let a_line = Expr::lam(BinderInfo::Default, interval(), a_iv.abstract_fvar(iv));
        // a' = coe (λ i. A i) r s a.
        let a_prime = coe(a_line.clone(), r.clone(), s.clone(), a_field.clone());
        // fillA at iv = coe (λ i. A i) r iv a — the coe-filler of `a` (variable
        // target `iv`); `fillA r ≡ a` (degenerate), `fillA s ≡ a'`.
        let fill_at_iv = coe(a_line.clone(), r.clone(), Expr::fvar(iv), a_field.clone());
        // B iv (fillA iv) — instantiate the Σ family at the filler.
        let b_applied = Expr::app(b_iv.clone(), fill_at_iv);
        // B_line = λ i. B i (fillA i)  (abstract iv: the inner `iv`s — both in `B`
        // and the filler's target — become the bound interval variable).
        let b_line = Expr::lam(BinderInfo::Default, interval(), b_applied.abstract_fvar(iv));
        // b' = coe (λ i. B i (fillA i)) r s b.
        let b_prime = coe(b_line, r.clone(), s.clone(), b_field.clone());

        // A s, B s — the result pair's type arguments (line at the target `s`).
        let a_s = a_iv.subst_fvar(iv, s);
        let b_s = b_iv.subst_fvar(iv, s);

        Some(Expr::apps(
            Expr::const_(sigma_names::SIGMA_MK.clone(), vec![level]),
            [a_s, b_s, a_prime, b_prime],
        ))
    }

    /// Coercion over a **(non-dependent) Path line**
    /// `λ i. Path (A i) (u i) (v i)` — the CCHM comp for the path type:
    ///
    /// ```text
    /// coe (λ i. Path (A i) (u i) (v i)) r s p
    ///   ↝ <j> comp (λ i. A i) [ (j=0) ↦ (λ i. u i), (j=1) ↦ (λ i. v i) ] (p @ j)
    /// ```
    ///
    /// where the inner `comp^{i:r→s} L [φ↦w] base` is assembled from the existing
    /// `hcomp` (i0→i1) and `coe` primitives plus the interval connections:
    ///
    /// ```text
    /// comp^{i:r→s} L [φ↦w] base
    ///   := hcomp {L s} [ φ ↦ λ k. coe (λ i. L i) (interp k) s (w (interp k)) ]
    ///                  (coe (λ i. L i) r s base)
    ///   interp k := (r ∧ ~k) ∨ (s ∧ k)        -- the De Morgan line from r (k=0) to s (k=1)
    /// ```
    ///
    /// ## Scope: non-dependent `Path` only (`PathP` stays stuck — sound)
    ///
    /// The two tubes `λ i. u i` / `λ i. v i` give the wall body
    /// `coe (λ i. L i) (interp k) s (w (interp k))`, whose `coe` base
    /// `w (interp k) : A(interp k)` must have the line type `L (interp k)`. For a
    /// **dependent** `PathP (λ j. A i j) …` the wall's `coe` base would need type
    /// `A (interp k) j` for a *generic* `j`, which holds only on the face — but the
    /// `System.cons` tube typing is **total** (`head : I → A`), so the dependent
    /// wall is ill-typed off-face and the reduct would not type-check. We therefore
    /// fire ONLY when the path family `A i` is constant in the path interval
    /// (the `ty` family ignores its argument); the dependent form is left **stuck**
    /// (`None`, sound).
    ///
    /// ## Value-correctness (conformance, not just typing)
    ///
    /// * **constant Path line** ⇒ the earlier constant-family rules fire first
    ///   (`coe ↝ base`), so this rule never sees a degenerate line;
    /// * **endpoints**: `(coe(Path) p) @ i0` path-beta's `j:=i0`, making the
    ///   `(j=0)` face `⊤`; the on-a-true-face `hcomp` rule gives
    ///   `wall0 @ i1 = coe (λ i. L i) (interp i1) s (u (interp i1)) = coe … s s (u s)
    ///   ≡ u s` (`interp i1 ⇓ s`, then degenerate `coe`). Symmetrically `@ i1 ≡ v s`.
    ///   The reduct is a genuine path with the coerced endpoints.
    /// * type preservation: `<j> comp … : Path (A s) (u s) (v s)`, the original line
    ///   at `s`. The hcomp's cap holds on each face (`u r ≡ p@i0`, `v r ≡ p@i1`).
    ///
    /// `line` is the already-WHNF'd coercion line `λ i. P[i]`; `base` (= `p`) is the
    /// path being coerced.
    fn try_coe_path(
        &self,
        line: &Expr,
        r: &Expr,
        s: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        // Cubical-only (mirrors the gating of `try_coe_glue_compute`).
        if !self.mode.has_cubical_layer() {
            return None;
        }
        let ExprKind::Lam(_, _dom_i, p_body) = line.kind() else {
            return None;
        };
        let save_len = self.ctx_len();
        let iv = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        // Expose the per-point type `Path (A iv) (u iv) (v iv)`.
        let p_open = self.whnf_recurse(&self.open_bvar(p_body, iv), mode);
        let result = self.coe_path_line(&p_open, iv, r, s, base, mode);
        self.ctx_truncate_to(save_len);
        result
    }

    /// Assemble the `coe`-over-Path reduct for the opened per-point type
    /// `p_open = Path (A iv) (u iv) (v iv)` (under the fresh interval binder `iv`).
    /// Returns `None` (⇒ caller stays stuck, sound) unless `p_open` is a
    /// `CubicalPath` whose family `A iv` is **constant** in the path interval
    /// (non-dependent `Path`; see [`Self::try_coe_path`]).
    fn coe_path_line(
        &self,
        p_open: &Expr,
        iv: FVarId,
        r: &Expr,
        s: &Expr,
        base: &Expr,
        mode: WhnfMode,
    ) -> Option<Expr> {
        let ExprKind::CubicalPath {
            ty: a_fam,
            left: u_i,
            right: v_i,
        } = p_open.kind()
        else {
            return None;
        };
        // Non-dependent only: the family `A iv : I → Sort u` must ignore its own
        // (path) interval argument. WHNF to a literal `λ j. C`; require `C` not to
        // mention `j` (`BVar 0`). A dependent `PathP` (or a neutral family) ⇒ stuck.
        let a_fam_w = self.whnf_recurse(a_fam, mode);
        let ExprKind::Lam(_, _, c_body) = a_fam_w.kind() else {
            return None;
        };
        if c_body.has_loose_bvar(0) {
            return None;
        }
        // A_iv = A iv @ i0 — the constant per-point base type (mentions `iv`).
        let i0 = || Expr::from_kind(ExprKind::CubicalI0);
        let interval = || Expr::from_kind(ExprKind::CubicalInterval);
        let a_iv = self.whnf_recurse(&Expr::app(a_fam_w.clone(), i0()), mode);
        let level = self.infer_sort(&a_iv).ok()?;

        // L = λ i. A i — the line of (path-)base types. Closed in `iv` after
        // abstraction; for the non-dependent case it carries no path interval.
        let l_line = Expr::lam(BinderInfo::Default, interval(), a_iv.abstract_fvar(iv));
        // The endpoint tubes as lines in the comp interval: w0 = λ i. u i, w1 = λ i. v i.
        let w0 = Expr::lam(BinderInfo::Default, interval(), u_i.abstract_fvar(iv));
        let w1 = Expr::lam(BinderInfo::Default, interval(), v_i.abstract_fvar(iv));
        // The two corrected walls (each `: I → L s`, jv-independent).
        let wall0 = self.coe_path_wall(&l_line, r, s, &w0);
        let wall1 = self.coe_path_wall(&l_line, r, s, &w1);
        // L s — the element type of the inner `hcomp`.
        let l_s = Expr::app(l_line.clone(), s.clone());

        // Outer path binder `<j>` (the produced path's own interval).
        let jv = self.ctx_push(Name::anon(), interval(), BinderInfo::Default);
        let j = Expr::fvar(jv);
        let cofib_eq0 =
            |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
        let cofib_eq1 =
            |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
        let cofib_or = |x: Expr, y: Expr| {
            Expr::apps(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), [x, y])
        };
        let face0 = cofib_eq0(j.clone());
        let face1 = cofib_eq1(j.clone());

        // floor' = coe (λ i. L i) r s (p @ j) — coerce the path point along the base
        // line. `p @ j : A r` (homogeneous path), `floor' : L s = A s`.
        let floor = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(base.clone()),
            arg: Arc::new(j.clone()),
        });
        let floor_coe = Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(l_line),
            r: Arc::new(r.clone()),
            s: Arc::new(s.clone()),
            base: Arc::new(floor),
        });

        // System `[ (j=0) ↦ wall0, (j=1) ↦ wall1 ]` at element type `L s`.
        let levels = vec![level];
        let sys_cons = |face: Expr, head: Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(kan_names::SYSTEM_CONS.clone(), levels.clone()),
                [l_s.clone(), face, head, tail],
            )
        };
        let sys_nil = Expr::app(
            Expr::const_(kan_names::SYSTEM_NIL.clone(), levels.clone()),
            l_s.clone(),
        );
        let system = sys_cons(
            face0.clone(),
            wall0,
            sys_cons(face1.clone(), wall1, sys_nil),
        );
        let phi = cofib_or(face0, face1);

        let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(l_s),
            phi: Arc::new(phi),
            u: Arc::new(system),
            base: Arc::new(floor_coe),
        });
        // Reduct = <j> Body — abstract the outer path interval `jv`.
        Some(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(hcomp.abstract_fvar(jv)),
        }))
    }

    /// Build a single corrected `comp` wall for [`Self::coe_path_line`]:
    ///
    /// ```text
    /// wall := λ k. coe (λ i. L i) (interp k) s (tube (interp k))
    ///   interp k := (r ∧ ~k) ∨ (s ∧ k)   -- the De Morgan line: interp i0 ⇓ r, interp i1 ⇓ s
    /// ```
    ///
    /// At the hcomp floor end `k = i0` the wall is `coe L r s (tube r)` (matching
    /// the floor `coe L r s base` on the wall's face, since `tube r ≡ base@(face)`);
    /// at the lid end `k = i1` it is `coe L s s (tube s) ≡ tube s` (the degenerate
    /// `coe`) — so the on-a-true-face `hcomp` rule recovers the coerced endpoint.
    /// `l_line`, `r`, `s`, `tube` are valid in the caller's context; the fresh `k`
    /// (`kv`) is `abstract_fvar`'d out into the tube lambda.
    fn coe_path_wall(&self, l_line: &Expr, r: &Expr, s: &Expr, tube: &Expr) -> Expr {
        let save_len = self.ctx_len();
        let kv = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        let k = Expr::fvar(kv);
        let i_min =
            |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MIN.clone(), vec![]), [x, y]);
        let i_max =
            |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MAX.clone(), vec![]), [x, y]);
        let i_neg = |x: Expr| Expr::app(Expr::const_(conn_names::I_NEG.clone(), vec![]), x);
        // interp k = (r ∧ ~k) ∨ (s ∧ k).
        let interp = i_max(
            i_min(r.clone(), i_neg(k.clone())),
            i_min(s.clone(), k.clone()),
        );
        // coe (λ i. L i) (interp k) s (tube (interp k)).
        let wall_body = Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(l_line.clone()),
            r: Arc::new(interp.clone()),
            s: Arc::new(s.clone()),
            base: Arc::new(Expr::app(tube.clone(), interp)),
        });
        let wall = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::CubicalInterval),
            wall_body.abstract_fvar(kv),
        );
        self.ctx_truncate_to(save_len);
        wall
    }

    /// Decide whether a type-family line body (under its interval binder, de
    /// Bruijn index 0) is *constant* in the interval variable. Two sound checks
    /// (a `true` result guarantees constancy):
    /// 1. **Syntactic** — the body does not mention the bound interval variable.
    /// 2. **Reductive** — open the binder with a fresh interval `FVar`, WHNF, and
    ///    check the fresh variable does not survive. Never reports a non-constant
    ///    line as constant (on doubt it returns `false`, leaving coercion stuck).
    fn coe_line_body_is_constant(&self, body: &Expr, mode: WhnfMode) -> bool {
        if !body.has_loose_bvar(0) {
            return true;
        }
        let save_len = self.ctx_len();
        let id = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        let opened = self.open_bvar(body, id);
        let opened_whnf = self.whnf_recurse(&opened, mode);
        let mentions_var = opened_whnf.abstract_fvar(id).has_loose_bvar(0);
        self.ctx_truncate_to(save_len);
        !mentions_var
    }

    /// **Deep** constant-family detection — the sound strengthening of
    /// [`Self::coe_line_body_is_constant`] that makes the `J` β-rule fire.
    ///
    /// A coercion line `λ i. B[i]` is *degenerate* (so `coe` is the identity)
    /// when `B` does not depend on the interval variable. The cheap check only
    /// WHNFs the opened body, so it misses constancy hidden inside the arguments
    /// of a neutral head or under a path-lambda — exactly the shape of the `J`
    /// motive line `λ i. P (p@i) (<j> p@(I.min i j))`, which becomes
    /// `λ i. P a (<j> a)` (i-independent) once `p = refl a` lets path-beta discard
    /// the interval argument.
    ///
    /// This check opens the body at a **fresh generic** interval point `id` and
    /// asks whether `B[id]` is definitionally equal to `B[i0]`. Because `id` is a
    /// fresh variable, convertibility holds *parametrically* — `B` takes a
    /// def-eq-constant value at every interval point — which is exactly genuine
    /// i-independence up to def-eq. The full `is_def_eq` reduces under binders and
    /// through neutral spines, so it sees the `refl`-collapse the cheap check
    /// cannot.
    ///
    /// SOUNDNESS: `coe A r s base ↝ base` is type-preserving and is the identity
    /// precisely for a degenerate line; keying the decision on the trusted
    /// `is_def_eq` makes a positive result exactly as trustworthy as the kernel's
    /// conversion check. Crucially it **never** reports a genuinely-varying line
    /// as constant — in particular the univalence line
    /// `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, idEquiv)]` is correctly rejected:
    /// `B[id]` is a *neutral* `Glue` (its faces `(id=0)`/`(id=1)` are neither ⊤
    /// nor ⊥) while `B[i0]` boundary-reduces to `A`, so `is_def_eq(B[id], B[i0])`
    /// is `false` and coercion proceeds to the genuine `ua` computation rule
    /// (`Equiv.fwd e x`) rather than collapsing transport to the identity.
    fn coe_line_constant_deep(&self, body: &Expr, _mode: WhnfMode) -> bool {
        if !self.mode.has_cubical_layer() {
            return false;
        }
        let save_len = self.ctx_len();
        let id = self.ctx_push(
            Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        let at_generic = self.open_bvar(body, id);
        let at_i0 = body.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        let result = self.is_def_eq(&at_generic, &at_i0);
        self.ctx_truncate_to(save_len);
        result
    }

    /// Parse a **Glue system** `sys` into its cells `[(φᵢ, Tᵢ, eᵢ)]`, each
    /// carrying a face `φᵢ`, a type `Tᵢ : Sort u`, and an equivalence
    /// `eᵢ : Equiv Tᵢ B` (Glue Phase 0–2).
    ///
    /// Recognises the reserved encoding
    /// `Glue.Sys.cons B φᵢ Tᵢ eᵢ (… Glue.Sys.nil B)`. Returns `None` (⇒ the
    /// caller leaves the Glue/unglue term **stuck**, which is sound) when the
    /// spine WHNFs to a neutral head that is neither `Glue.Sys.cons` nor
    /// `Glue.Sys.nil`. One shared interner keeps interval-variable atom ids
    /// consistent across the cell faces (so `parse_cofib` of each `φᵢ` is mutually
    /// meaningful), exactly as in [`Self::parse_system`].
    pub(in crate::tc) fn parse_glue_system(
        &self,
        sys: &Expr,
        mode: WhnfMode,
    ) -> Option<Vec<(Cofib, Expr, Expr)>> {
        let mut interner: Vec<Expr> = Vec::new();
        let mut cells: Vec<(Cofib, Expr, Expr)> = Vec::new();
        let mut cur = sys.clone();
        loop {
            let w = self.whnf_recurse(&cur, mode);
            let ExprKind::Const(name, _) = w.get_app_fn().kind() else {
                return None;
            };
            let args = w.get_app_args();
            if *name == *glue_names::GLUE_SYS_CONS && args.len() == 6 {
                // args = [B, φ, T, e, ie, tail]. The carried `ie` (isEquiv witness,
                // arg 4) is not needed by the Glue-type / unglue boundary rules that
                // call this parser — it is read directly from the cell by the
                // residual `coe`-over-`Glue` rule via `match_glue_cons`.
                let cof = self.parse_cofib(args[1], &mut interner, mode)?;
                cells.push((cof, args[2].clone(), args[3].clone()));
                cur = args[5].clone();
                continue;
            }
            if *name == *glue_names::GLUE_SYS_NIL {
                return Some(cells);
            }
            return None;
        }
    }

    /// Attempt one head-reduction step for an encoded **Glue / unglue** redex
    /// (Glue Phase 0–2). `head` is the spine-head constant of `e` (already
    /// extracted by the WHNF trampoline). Only called in `Cubical` mode.
    ///
    /// Three type-preserving rules:
    /// * **Glue boundary** (the rule that makes `ua` type-check) —
    ///   `Glue B φ [… φᵢ↦(Tᵢ,eᵢ) …]` where the first cell whose face `φᵢ ⇓ ⊤`
    ///   fixes the result: `↝ Tᵢ`. Type-preserving because `Glue … : Sort u` and
    ///   the cell's `Tᵢ : Sort u` (forced by `Glue.Sys.cons`'s axiom type).
    ///   **Deterministic** — first total cell, mirroring
    ///   [`Self::try_hcomp_reduction`]'s on-a-true-face rule. Determinism is what
    ///   keeps this sound without a separate overlap-agreement check: distinct
    ///   types are never *equated*, only one is canonically chosen (see the
    ///   module/SOUNDNESS notes).
    /// * **unglue β** — `unglue B φ sys (glue B T φ e t a) ↝ a`. Type-preserving
    ///   because `unglue … : B` and `a : B` (forced by `glue`'s axiom type).
    /// * **Equiv.fwd β** (the *computing projection* that makes
    ///   `transport (ua e) x` reduce concretely) —
    ///   `Equiv.fwd A B (Equiv.mk A' B' f g η ε) [x…] ↝ f [x…]` and
    ///   `Equiv.fwd A A (Equiv.idEquiv A') [x…] ↝ (λ z:A'. z) [x…]`. Type-preserving
    ///   because `Equiv.fwd A B e : A→B` and the projected `f : A→B` (forced by
    ///   `Equiv.mk`'s axiom type); the identity case is the `idEquiv` instance.
    ///   Fires ONLY when the equivalence argument WHNFs to a literal `Equiv.mk` /
    ///   `Equiv.idEquiv` — a **neutral** equivalence (a variable, an opaque axiom
    ///   like the `ua` cells' `e`) stays stuck, which is what keeps the rule from
    ///   over-firing.
    ///
    /// Everything else (neutral system, no total cell, non-`glue` argument,
    /// `Equiv.fwd`/`Equiv.bwd` on a neutral equivalence, wrong arity) is **stuck**
    /// (`None`). Transport over a `Glue` line (`coe`/`transp`) reduces via the
    /// general transp-over-`Glue` rule (see [`Self::try_coe_glue_compute`]) when a
    /// cell is total at `i1`; a residual Glue at `i1` stays stuck.
    pub(in crate::tc) fn try_glue_reduction(
        &self,
        e: &Expr,
        head: &Name,
        mode: WhnfMode,
    ) -> Option<Expr> {
        if *head == *glue_names::EQUIV_FWD || *head == *glue_names::EQUIV_BWD {
            // `Equiv.fwd {A B} (e : Equiv A B) [x…]` — the computing first
            // projection (`f`); `Equiv.bwd` is the dual backward projection (`g`).
            // Need at least the equivalence argument (explicit index 2, after the
            // two now-explicit type args A, B as the rule applies them).
            let is_fwd = *head == *glue_names::EQUIV_FWD;
            let args = e.get_app_args();
            if args.len() < 3 {
                return None;
            }
            let equiv = self.whnf_recurse(args[2], mode);
            let ExprKind::Const(ename, _) = equiv.get_app_fn().kind() else {
                return None;
            };
            // Trailing arguments after the equivalence (e.g. the point `x`), kept
            // applied to the projected map.
            let rest: Vec<Expr> = args.iter().skip(3).map(|a| (*a).clone()).collect();
            if *ename == *glue_names::EQUIV_MK {
                // Equiv.fwd A B (Equiv.mk A' B' f g η ε) [x…] ↝ f [x…]  (f = mk arg 2);
                // Equiv.bwd … ↝ g [x…]  (g = mk arg 3).
                let margs = equiv.get_app_args();
                if margs.len() == 6 {
                    let proj = if is_fwd { 2 } else { 3 };
                    return Some(Expr::apps(margs[proj].clone(), rest));
                }
                return None;
            }
            if *ename == *glue_names::EQUIV_ID {
                // Equiv.{fwd,bwd} A A (Equiv.idEquiv A') [x…] ↝ (λ z:A'. z) [x…]
                // (the identity equivalence's forward and backward maps coincide).
                let iargs = equiv.get_app_args();
                if iargs.len() == 1 {
                    let id_fn = Expr::lam(BinderInfo::Default, iargs[0].clone(), Expr::bvar(0));
                    return Some(Expr::apps(id_fn, rest));
                }
                return None;
            }
            return None;
        }
        if *head == *glue_names::GLUE {
            let args = e.get_app_args();
            if args.len() != 3 {
                return None;
            }
            let cells = self.parse_glue_system(args[2], mode)?;
            for (cof, t_ty, _equiv) in &cells {
                if cof.is_top() {
                    return Some(t_ty.clone());
                }
            }
            return None;
        }
        if *head == *glue_names::UNGLUE {
            let args = e.get_app_args();
            if args.len() != 4 {
                return None;
            }
            // (1) unglue β — the literal-`glue`-intro projection (takes priority over
            // the total-face rule below, so `unglue (glue … a) ↝ a` even on ⊤).
            let g = self.whnf_recurse(args[3], mode);
            if let ExprKind::Const(gname, _) = g.get_app_fn().kind() {
                if *gname == *glue_names::GLUE_INTRO {
                    // glue B T φ e ie t a — project the underlying `a : B` (arg 6).
                    let gargs = g.get_app_args();
                    if gargs.len() == 7 {
                        return Some(gargs[6].clone());
                    }
                }
            }
            // (2) unglue total-face — the boundary rule dual to the `Glue`-type
            // boundary: when the first system cell's face `φₖ ⇓ ⊤`, the Glue type
            // degenerates to `Tₖ` and `unglue` restricts to that cell's forward
            // map: `unglue B φ [φₖ↦(Tₖ,eₖ)…] g ↝ Equiv.fwd eₖ g`. This is what lets
            // `unglue` of a *non-`glue`-intro* element (e.g. a raw value typed
            // through the degenerate `Glue B ⊤ … ≡ Tₖ`) compute — needed by the
            // general `transp`-over-`Glue` rule at the `i0` endpoint. Type-preserving:
            // on φₖ⊤, `g : Tₖ` and `Equiv.fwd eₖ : Tₖ → B`. Only fires in the encoded
            // single-universe `Glue`; the level comes from the `unglue` head.
            let ExprKind::Const(_, levels) = e.get_app_fn().kind() else {
                return None;
            };
            let level = levels.first()?.clone();
            let b_base = args[0].clone();
            let cells = self.parse_glue_system(args[2], mode)?;
            for (cof, t_ty, equiv) in &cells {
                if cof.is_top() {
                    return Some(Expr::apps(
                        Expr::const_(glue_names::EQUIV_FWD.clone(), vec![level]),
                        [t_ty.clone(), b_base, equiv.clone(), args[3].clone()],
                    ));
                }
            }
            return None;
        }
        None
    }

    /// Attempt one head-reduction step for an encoded **dependent-sum (`Σ`)
    /// eliminator** redex — the `Sigma`-iota / `β`-rule for the dependent pair:
    ///
    /// ```text
    /// Sigma.elim A B M m (Sigma.mk A' B' a b) [x…]  ↝  m a b [x…]
    /// ```
    ///
    /// `head` is the spine-head constant of `e` (already extracted by the WHNF
    /// trampoline). Only called in `Cubical` mode (gated at the call site in
    /// `whnf.rs`, mirroring [`Self::try_glue_reduction`]).
    ///
    /// ## When it fires (and why it cannot over-fire)
    ///
    /// Fires ONLY when the scrutinee (the `Sigma.elim`'s 5th explicit argument `p`)
    /// WHNFs to a **literal `Sigma.mk`** (reserved head, arity 4 — `A' B' a b`).
    /// A *neutral* Σ point (a variable, an opaque axiom, a stuck `coe`/`Sigma.elim`)
    /// stays stuck (`None`), exactly as the `Equiv.fwd`/`unglue`-β rules stay stuck
    /// on a neutral equivalence / non-`glue` element. Any other head, or wrong
    /// arity on either constant, is stuck. Trailing arguments past `p` (over-
    /// application, possible because `M p` may itself be a function type) are kept
    /// applied to the contractum.
    ///
    /// ## SOUNDNESS: standard `Σ`-iota, type-preserving
    ///
    /// This is precisely the defining computation rule of the dependent-sum
    /// eliminator registered by [`register_sigma_axioms`]
    /// (`Sigma.elim A B M m (Sigma.mk A B a b) = m a b`), so it is interpretable by
    /// the genuine dependent sum and adds no inconsistency. Type preservation: in a
    /// well-typed redex `p = Sigma.mk A' B' a b : Sigma A B` forces `A' ≡ A`,
    /// `B' ≡ B` (def-eq), `a : A`, `b : B a`; the minor
    /// `m : (a:A) → (b:B a) → M (Sigma.mk A B a b)` gives `m a b : M (Sigma.mk A B a b)`,
    /// which is def-eq to the redex's type `M p`. Like the kernel's other iota rules,
    /// it is applied during WHNF without re-checking — the reduct's *value* is the
    /// minor applied to the literal pair's components, never a different one, so the
    /// rewrite is meaning-preserving.
    pub(in crate::tc) fn try_sigma_reduction(
        &self,
        e: &Expr,
        head: &Name,
        mode: WhnfMode,
    ) -> Option<Expr> {
        if *head != *sigma_names::SIGMA_ELIM {
            return None;
        }
        let args = e.get_app_args();
        // Sigma.elim A B M m p [rest…] — need the five explicit arguments.
        if args.len() < 5 {
            return None;
        }
        let minor = args[3];
        // The scrutinee must WHNF to a literal `Sigma.mk A' B' a b`.
        let scrut = self.whnf_recurse(args[4], mode);
        let ExprKind::Const(mk_name, _) = scrut.get_app_fn().kind() else {
            return None;
        };
        if *mk_name != *sigma_names::SIGMA_MK {
            return None;
        }
        let mk_args = scrut.get_app_args();
        if mk_args.len() != 4 {
            return None;
        }
        // `m a b` — the minor applied to the pair's components (a = mk arg 2,
        // b = mk arg 3), then any trailing over-applied arguments past `p`.
        let mut reduct = Expr::apps(minor.clone(), [mk_args[2].clone(), mk_args[3].clone()]);
        if args.len() > 5 {
            let rest: Vec<Expr> = args.iter().skip(5).map(|a| (*a).clone()).collect();
            reduct = Expr::apps(reduct, rest);
        }
        Some(reduct)
    }

    /// Attempt one head-reduction step for an encoded **interval connection**
    /// (`I.min`, `I.max`, `I.neg`). `head` is the spine-head constant of `e`
    /// (already extracted by the WHNF trampoline). Only called in `Cubical` mode
    /// (gated at the call site in `whnf.rs`, mirroring [`Self::try_glue_reduction`]).
    ///
    /// The interval `I` is a **De Morgan lattice**: meet `I.min` (∧), join
    /// `I.max` (∨), and an involutive order-reversing complement `I.neg` (~).
    /// The rules below are precisely its laws — every reduct is again
    /// *interval-valued*, so they are type-preserving (`I → I`) and prove nothing
    /// false:
    ///
    /// ```text
    /// I.min i0 r ↝ i0   I.min i1 r ↝ r    I.min r i0 ↝ i0   I.min r i1 ↝ r   I.min r r ↝ r
    /// I.max i0 r ↝ r    I.max i1 r ↝ i1   I.max r i0 ↝ r    I.max r i1 ↝ i1  I.max r r ↝ r
    /// I.neg i0 ↝ i1     I.neg i1 ↝ i0     I.neg (I.neg r) ↝ r
    /// ```
    ///
    /// A fully-neutral redex stays **stuck** (`None`): `min`/`max` of two
    /// arguments with no literal endpoint and not definitionally equal, or `neg`
    /// of a neutral term that is not itself a `neg`. A stuck interval term is
    /// sound. SOUNDNESS: lattice identities are unconditionally valid in any De
    /// Morgan algebra; the idempotency arm fires only when the two operands are
    /// `is_def_eq` (genuinely the same point), so it can never equate distinct
    /// interval variables.
    pub(in crate::tc) fn try_interval_connection_reduction(
        &self,
        e: &Expr,
        head: &Name,
        mode: WhnfMode,
    ) -> Option<Expr> {
        let i0 = || Expr::from_kind(ExprKind::CubicalI0);
        let i1 = || Expr::from_kind(ExprKind::CubicalI1);

        if *head == *conn_names::I_NEG {
            let args = e.get_app_args();
            if args.len() != 1 {
                return None;
            }
            let a = self.whnf_recurse(args[0], mode);
            if matches!(a.kind(), ExprKind::CubicalI0) {
                return Some(i1());
            }
            if matches!(a.kind(), ExprKind::CubicalI1) {
                return Some(i0());
            }
            // I.neg (I.neg r) ↝ r — involutivity.
            if let ExprKind::Const(inner, _) = a.get_app_fn().kind() {
                if *inner == *conn_names::I_NEG {
                    let inner_args = a.get_app_args();
                    if inner_args.len() == 1 {
                        return Some(inner_args[0].clone());
                    }
                }
            }
            return None;
        }

        if *head == *conn_names::I_MIN || *head == *conn_names::I_MAX {
            let args = e.get_app_args();
            if args.len() != 2 {
                return None;
            }
            let is_min = *head == *conn_names::I_MIN;
            let x = self.whnf_recurse(args[0], mode);
            let y = self.whnf_recurse(args[1], mode);
            // Precompute endpoint flags so `x`/`y` can be moved into the reduct
            // without holding a borrow from a `match` scrutinee.
            let x0 = matches!(x.kind(), ExprKind::CubicalI0);
            let x1 = matches!(x.kind(), ExprKind::CubicalI1);
            let y0 = matches!(y.kind(), ExprKind::CubicalI0);
            let y1 = matches!(y.kind(), ExprKind::CubicalI1);
            // min: i0 is bottom (absorbing), i1 is top (unit).
            // max: i1 is top (absorbing), i0 is bottom (unit).
            return if x0 {
                Some(if is_min { i0() } else { y })
            } else if x1 {
                Some(if is_min { y } else { i1() })
            } else if y0 {
                Some(if is_min { i0() } else { x })
            } else if y1 {
                Some(if is_min { x } else { i1() })
            } else if self.is_def_eq(&x, &y) {
                // Idempotency r r ↝ r (both fully neutral but definitionally equal).
                Some(x)
            } else {
                None
            };
        }

        None
    }
}

/// Build the **path composition** `p ∙ q` (Deliverable C).
///
/// For `p : Path A a b` and `q : Path A b c` (with `a_type` the underlying type
/// `A : Sort u` carrying `level = u`), this returns the CCHM `compPath` square
///
/// ```text
/// p ∙ q := <i> hcomp {A} [ (i=0) ↦ λ j. p@i,  (i=1) ↦ λ j. q@j ] (p@i)
/// ```
///
/// which has type `Path A a c`, with `(p ∙ q) @ i0 ≡ a` and `(p ∙ q) @ i1 ≡ c`.
///
/// ## de Bruijn discipline
///
/// The outer `<i>` (`CubicalPathLam`) binds interval `BVar(0)` throughout the
/// `hcomp` body (the face/system/base fields add no binders of their own, so the
/// faces `Cofib.eq0/eq1 (BVar 0)` and the base `p @ (BVar 0)` reference `i`
/// directly). Each tube branch is an **ordinary** interval function `λ j:I. …`
/// (a `Lam` of type `I → A`, *not* a path-lam), so inside a branch `i` shifts to
/// `BVar(1)` while its own `j` is `BVar(0)`:
/// * `branch (i=0)` = `λ j. p@i` = `Lam(I, p @ BVar(1))` — constant in `j`, value
///   `p@i` (which is `a` on the face `i=0`).
/// * `branch (i=1)` = `λ j. q@j` = `Lam(I, q @ BVar(0))` — value `q@i1 = c` on the
///   face `i=1`.
///
/// On `(p∙q)@i0` the path-beta substitutes `i := i0`, the `(i=0)` face becomes
/// `⊤`, and `try_hcomp_reduction` fires the on-a-true-face rule to
/// `(λ j. p@i0) i1 ≡ p@i0 ≡ a`; symmetrically `(p∙q)@i1 ≡ q@i1 ≡ c`.
// Not yet wired to a production caller (the elaborator surface for `∙` is future
// work); exercised by the path-composition soundness tests.
#[allow(dead_code)]
pub(crate) fn path_compose(a_type: &Expr, level: Level, p: &Expr, q: &Expr) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let path_app = |path: &Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path.clone()),
            arg: Arc::new(arg),
        })
    };

    // φ = (i=0) ∨ (i=1), with i = BVar(0) at the hcomp level.
    let phi = Expr::app(
        Expr::app(
            Expr::const_(kan_names::COFIB_OR.clone(), vec![]),
            cofib_eq0(Expr::bvar(0)),
        ),
        cofib_eq1(Expr::bvar(0)),
    );

    // Tube branches: ordinary functions I → A. Inside the `λ j`, i = BVar(1).
    let branch_i0 = Expr::lam(BinderInfo::Default, interval(), path_app(p, Expr::bvar(1)));
    let branch_i1 = Expr::lam(BinderInfo::Default, interval(), path_app(q, Expr::bvar(0)));

    let levels = vec![level];
    let sys_cons = |a: Expr, face: Expr, head: Expr, tail: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(kan_names::SYSTEM_CONS.clone(), levels.clone()),
                        a,
                    ),
                    face,
                ),
                head,
            ),
            tail,
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), levels.clone()),
        a_type.clone(),
    );
    let system = sys_cons(
        a_type.clone(),
        cofib_eq0(Expr::bvar(0)),
        branch_i0,
        sys_cons(a_type.clone(), cofib_eq1(Expr::bvar(0)), branch_i1, sys_nil),
    );

    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a_type.clone()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(path_app(p, Expr::bvar(0))),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// Build the **constant (reflexivity) path** `refl a := <i> a` (the obvious
/// groupoid identity).
///
/// For `a : A` this returns the `CubicalPathLam` whose body ignores the bound
/// interval, so `refl a : Path (λ_. A) a a` with `(refl a) @ r ≡ a` at every
/// endpoint `r` (path-beta `(<i> a) @ r ↝ a`, since `a` is closed in `i`).
///
/// ## de Bruijn discipline
///
/// The outer `<i>` (`CubicalPathLam`) binds interval `BVar(0)`, but the body `a`
/// is assumed **closed** (no loose `BVar(0)`), so it references neither the
/// interval nor any other binder — exactly the constancy that makes this the
/// reflexivity path.
// Not yet wired to a production caller (the elaborator surface for `refl` is
// future work); exercised by the groupoid-law soundness tests.
#[allow(dead_code)]
pub(crate) fn path_refl(a: &Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(a.clone()),
    })
}

/// Build the **path inverse** `sym p` (Rung-1 groupoid law `sym`).
///
/// For `p : Path A a b` (with `a_type` the underlying type `A : Sort u` carrying
/// `level = u`, and `a = p @ i0` recovered internally), this returns the standard
/// cubical inverse square
///
/// ```text
/// sym p := <i> hcomp {A} [ (i=0) ↦ λ j. p @ j,  (i=1) ↦ λ j. a ] a       -- a = p @ i0
/// ```
///
/// which has type `Path A b a`, with `(sym p) @ i0 ≡ b` and `(sym p) @ i1 ≡ a`.
///
/// ## de Bruijn discipline
///
/// Mirrors [`path_compose`]. The outer `<i>` (`CubicalPathLam`) binds interval
/// `BVar(0)` throughout the `hcomp` body (the face/system/base fields add no
/// binders of their own, so the faces `Cofib.eq0/eq1 (BVar 0)` reference `i`
/// directly). Each tube branch is an **ordinary** interval function `λ j:I. …`
/// (a `Lam` of type `I → A`, *not* a path-lam), so inside a branch `i` shifts to
/// `BVar(1)` while its own `j` is `BVar(0)`:
/// * `branch (i=0)` = `λ j. p@j` = `Lam(I, p @ BVar(0))` — the "diagonal" wall,
///   value `p@j` (which is `p@i1 = b` once the lid is read at `j=i1`).
/// * `branch (i=1)` = `λ j. a` = `Lam(I, a)` — constant in `j`, value `a`
///   (`a = p@i0` is closed in both `i` and `j`).
/// * `base` = `a = p@i0` (closed; references no binder).
///
/// On `(sym p)@i0` the path-beta substitutes `i := i0`, the `(i=0)` face becomes
/// `⊤`, and [`Self::try_hcomp_reduction`] fires the on-a-true-face rule to
/// `(λ j. p@j) i1 ≡ p@i1 ≡ b`; symmetrically on `(sym p)@i1` the `(i=1)` face is
/// `⊤` and the lid is `(λ j. a) i1 ≡ a`.
///
/// SOUNDNESS: this is the standard CCHM definitional `sym`, a type-preserving
/// construction — both tubes `: I → A` and the floor `a : A`, so the `hcomp`
/// lands in `A` and the assembled `<i> …` has type `Path A b a`. The endpoints
/// are not asserted; they *compute* through the existing on-a-true-face hcomp
/// rule and the neutral path-endpoint rule (`p@i1 ≡ b`, `p@i0 ≡ a`).
// Not yet wired to a production caller (the elaborator surface for `sym` is
// future work); exercised by the groupoid-law soundness tests.
#[allow(dead_code)]
pub(crate) fn path_sym(a_type: &Expr, level: Level, p: &Expr) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let path_app = |path: &Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path.clone()),
            arg: Arc::new(arg),
        })
    };
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);

    // a = p @ i0 — the left endpoint of `p`, closed in the interval binder.
    let a = path_app(p, i0());

    // φ = (i=0) ∨ (i=1), with i = BVar(0) at the hcomp level.
    let phi = Expr::app(
        Expr::app(
            Expr::const_(kan_names::COFIB_OR.clone(), vec![]),
            cofib_eq0(Expr::bvar(0)),
        ),
        cofib_eq1(Expr::bvar(0)),
    );

    // Tube branches: ordinary functions I → A. Inside the `λ j`, i = BVar(1)
    // (unused). `branch (i=0)` is the diagonal `λ j. p@j` (j = BVar(0));
    // `branch (i=1)` is the constant `λ j. a` (a is closed).
    let branch_i0 = Expr::lam(BinderInfo::Default, interval(), path_app(p, Expr::bvar(0)));
    let branch_i1 = Expr::lam(BinderInfo::Default, interval(), a.clone());

    let levels = vec![level];
    let sys_cons = |a_ty: Expr, face: Expr, head: Expr, tail: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(kan_names::SYSTEM_CONS.clone(), levels.clone()),
                        a_ty,
                    ),
                    face,
                ),
                head,
            ),
            tail,
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), levels.clone()),
        a_type.clone(),
    );
    let system = sys_cons(
        a_type.clone(),
        cofib_eq0(Expr::bvar(0)),
        branch_i0,
        sys_cons(a_type.clone(), cofib_eq1(Expr::bvar(0)), branch_i1, sys_nil),
    );

    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a_type.clone()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(a),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// Build the **regular path inverse** `sym_neg p := <i> p @ (I.neg i)` via
/// interval reversal (Rung-1 deliverable 2 — the *regular* `sym`).
///
/// For `p : Path A a b` this returns the path `<i> p @ (~i)`, which has type
/// `Path A b a`:
/// * `(sym_neg p) @ i0 ≡ p @ (~i0) ≡ p @ i1 ≡ b` (path-beta, then `I.neg i0 ↝ i1`,
///   then the neutral path-endpoint rule), and symmetrically `(sym_neg p)@i1 ≡ a`.
///
/// ## Why this is the *regular* `sym` (the regularity gap [`path_sym`] left open)
///
/// `sym_neg (refl a) ≡ refl a` holds **definitionally**, not just at the
/// endpoints. With `refl a = <k> a` (constant in its binder), path-beta discards
/// the reversed argument entirely: `(<k> a) @ (~i) ↝ a`, so
/// `sym_neg (refl a) = <i> (<k> a) @ (~i) ≡ <i> a = refl a`. The hcomp-based
/// [`path_sym`] only computes the endpoints of `sym (refl a)`; this reversal
/// version is the genuine involution on the nose.
///
/// ## de Bruijn discipline
///
/// The outer `<i>` (`CubicalPathLam`) binds interval `BVar(0)`; the only
/// occurrence of `i` is the argument `I.neg (BVar 0)`. The path `p` is assumed
/// **closed** (no loose `BVar(0)`), so it is unaffected by the binder.
// Not yet wired to a production caller (the elaborator surface for `sym` is
// future work); exercised by the regular-`sym` soundness tests.
#[allow(dead_code)]
pub(crate) fn path_sym_neg(p: &Expr) -> Expr {
    // ~i = I.neg (BVar 0), with i = BVar(0) under the outer `<i>`.
    let neg_i = Expr::app(
        Expr::const_(conn_names::I_NEG.clone(), vec![]),
        Expr::bvar(0),
    );
    let body = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p.clone()),
        arg: Arc::new(neg_i),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(body),
    })
}

/// Build **path induction** `J P d a p` (Rung-1 deliverable 3) as a transport
/// over the canonical contractible-singleton motive line:
///
/// ```text
/// J P d a p := transport (λ i. P (p @ i) (<j> p @ (I.min i j))) d
///            = coe^{i0→i1} (λ i. P (p @ i) (<j> p @ (i ∧ j))) d
/// ```
///
/// With `P : (y:A) → Path A a y → Sort l` the motive, `d : P a (refl a)` the
/// base case, and `p : Path A a y`, this has type `P y p`:
/// * the motive line at `i0` is `P (p@i0) (<j> p@(i0 ∧ j))`; `p@i0 ≡ a` and
///   `i0 ∧ j ↝ i0` give `<j> p@i0 ≡ <j> a ≡ refl a`, so it is `P a (refl a)` —
///   the type of `d` (this is the `coe` *base* check);
/// * the motive line at `i1` is `P (p@i1) (<j> p@(i1 ∧ j))`; `p@i1 ≡ y` and
///   `i1 ∧ j ↝ j` give `<j> p@j ≡ p` (path-eta), so the `coe` *result* is `P y p`.
/// Both rely on the `I.min` (∧) reductions firing on the neutral interval point.
///
/// ## β-rule (the headline): `J P d a (refl a) ≡ d` by COMPUTATION
///
/// With `p = refl a = <k> a`, path-beta makes `p@i ≡ a` and `p@(i∧j) ≡ a` for
/// any interval argument, so the motive line is the i-constant `λ i. P a (<j> a)`.
/// `coe` over a degenerate line is the identity, so it reduces to its base `d` —
/// fired by [`Self::coe_line_constant_deep`] (the deep constant-family rule).
///
/// ## de Bruijn discipline
///
/// The line binder `λ i` is `BVar(0)` in `BODY = P (p@i) (<j> p@(I.min i j))`;
/// `p@i` reads `i = BVar(0)`. Inside the inner `<j>` path-lam the binder `j` is
/// `BVar(0)` and `i` shifts to `BVar(1)`, so the diagonal is
/// `p @ (I.min (BVar 1) (BVar 0))`. `motive_p` and `p` are assumed **closed**.
// Not yet wired to a production caller (the elaborator surface for `J` is future
// work); exercised by the `J` β-rule / typing soundness tests.
#[allow(dead_code, non_snake_case)]
pub(crate) fn path_J(motive_p: &Expr, d: &Expr, p: &Expr) -> Expr {
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let i_min =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MIN.clone(), vec![]), [x, y]);

    // diag = <j> p @ (I.min i j); under <j>: i = BVar(1), j = BVar(0).
    let diag = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(path_app(p.clone(), i_min(Expr::bvar(1), Expr::bvar(0)))),
    });

    // BODY = P (p @ i) (<j> p @ (I.min i j)); i = BVar(0).
    let body = Expr::apps(motive_p.clone(), [path_app(p.clone(), Expr::bvar(0)), diag]);

    // line = λ i. BODY.
    let line = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        body,
    );

    // J P d a p := coe^{i0→i1} line d  (= transport over the motive line).
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
        s: Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
        base: Arc::new(d.clone()),
    })
}

/// Register the reserved cofibration / system constants (see [`kan_names`]) into a
/// **Cubical-mode** environment, with the interval-valued types that make the
/// Expr-encoding genuinely well-typed (`phi : I`, system `: I → A`). This lets the
/// existing inference, certificate builder and certificate verifier accept
/// multi-branch `hcomp` terms unchanged.
///
/// Idempotent-ish: callers should register once per environment. Returns the first
/// registration error if any.
// Not yet wired to a production caller (cubical environments are configured by
// tests for now); exercised by the path-composition / system soundness tests.
#[allow(dead_code)]
pub(crate) fn register_kan_system_axioms(
    env: &mut Environment,
) -> Result<(), crate::env::EnvError> {
    let i = || Expr::from_kind(ExprKind::CubicalInterval);
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));

    let mut axiom =
        |name: &str, level_params: Vec<Name>, type_: Expr| -> Result<(), crate::env::EnvError> {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params,
                type_,
            })
        };

    // Cofibration heads (interval-valued; no universe parameters).
    axiom("Cofib.top", vec![], i())?;
    axiom("Cofib.bot", vec![], i())?;
    axiom("Cofib.eq0", vec![], Expr::arrow(i(), i()))?;
    axiom("Cofib.eq1", vec![], Expr::arrow(i(), i()))?;
    axiom("Cofib.and", vec![], Expr::arrow(i(), Expr::arrow(i(), i())))?;
    axiom("Cofib.or", vec![], Expr::arrow(i(), Expr::arrow(i(), i())))?;

    // Interval connections — the De Morgan lattice on `I` (meet/join/reversal).
    // All interval-valued (so the encoding is genuinely well-typed); their
    // reduction rules live in `try_interval_connection_reduction`.
    axiom("I.min", vec![], Expr::arrow(i(), Expr::arrow(i(), i())))?;
    axiom("I.max", vec![], Expr::arrow(i(), Expr::arrow(i(), i())))?;
    axiom("I.neg", vec![], Expr::arrow(i(), i()))?;

    // System.cons.{u} : Π {A : Sort u} (φ:I) (head:I→A) (tail:I→A), I → A.
    // de Bruijn: A is BVar(1) at head's type position, BVar(2) inside head's
    // arrow, etc. (each `arrow` introduces one binder).
    let system_cons_ty = Expr::pi(
        BinderInfo::Implicit,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            i(),
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(i(), Expr::bvar(2)), // head : I → A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::arrow(i(), Expr::bvar(3)), // tail : I → A
                    Expr::arrow(i(), Expr::bvar(4)), // result : I → A
                ),
            ),
        ),
    );
    axiom("System.cons", vec![u.clone()], system_cons_ty)?;

    // System.nil.{u} : Π {A : Sort u}, I → A.
    let system_nil_ty = Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::arrow(i(), Expr::bvar(1)), // I → A
    );
    axiom("System.nil", vec![u], system_nil_ty)?;

    Ok(())
}

/// Register the reserved **Glue / univalence** constants (see [`glue_names`]) into
/// a **Cubical-mode** environment, with the interval/type-valued axiom types that
/// make the Expr-encoding genuinely well-typed. This lets the existing inference,
/// certificate builder and certificate verifier accept `Glue`/`glue`/`unglue`/`ua`
/// terms unchanged (they are plain `Const`/`App` spines).
///
/// The Glue-system cell faces are encoded with the `Cofib.*` heads, so callers
/// that build encoded systems must also register [`register_kan_system_axioms`].
///
/// SOUNDNESS of the axiom set:
/// * `Equiv` is now a **structured** type former: `Equiv.mk` is its constructor
///   and `Equiv.fwd` its computing first projection — i.e. `Equiv A B` is the
///   record `{ f:A→B, g:B→A, η:g∘f~id, ε:f∘g~id }`. A record over consistent
///   field types is consistent (it is inhabited, e.g. `A≡B, f=g=id, η=ε=refl`),
///   and a projection with its β-rule introduces no inconsistency. Demanding the
///   full inverse data means `Equiv A B` cannot be fabricated between
///   logically-inequivalent types, so `ua` only transports along genuine
///   equivalences. `Glue.Sys` stays an **opaque** type former with ordinary value
///   axioms (`Glue.Sys.cons/nil`) — opaque types with asserted inhabitants never
///   introduce inconsistency (no eliminator, no relation to other types).
/// * `glue` builds its **own single-cell** system `[φ↦(T,e)]` (trivially
///   coherent — no overlaps). Its conclusion `Glue B φ [φ↦(T,e)]` is inhabited in
///   the intended cubical model whenever `B` is (take `a:B` and the partial
///   element `e⁻¹(a):T` forced by the equivalence), so asserting it as an axiom is
///   consistency-preserving. The extra premise `t:T` is unused by that model
///   witness; not enforcing the boundary `e(t)=a` only makes the axiom *weaker*
///   (still inhabited), never unsound.
/// * `unglue`'s result is `B` independent of its `Glue` argument — sound by
///   construction.
///
/// Idempotent-ish: register once per environment. Returns the first registration
/// error if any.
// Not yet wired to a production caller (cubical environments are configured by
// tests for now); exercised by the Glue / univalence soundness tests.
#[allow(dead_code)]
pub(crate) fn register_glue_axioms(env: &mut Environment) -> Result<(), crate::env::EnvError> {
    // The carried-`isEquiv` cell witness (`Glue.Sys.cons`'s `ie` field and
    // `Equiv.toIsEquiv`'s result type) is the `Sigma`-encoded contractible-fibre
    // `isEquiv (Equiv.fwd e)`, so the dependent-sum former must be present before
    // those axiom types are checked. `register_sigma_axioms` is idempotent, so a
    // caller that *also* registers `Sigma` directly (in either order) is fine.
    register_sigma_axioms(env)?;
    let i = || Expr::from_kind(ExprKind::CubicalInterval);
    let u = Name::from_string("u");
    let lu = Level::param(u.clone());
    let sort_u = Expr::sort(lu.clone());

    // Reserved const heads at level `u` (cloned per-use below).
    let equiv = Expr::const_(glue_names::EQUIV.clone(), vec![lu.clone()]);
    let glue_sys = Expr::const_(glue_names::GLUE_SYS.clone(), vec![lu.clone()]);
    let glue_sys_cons = Expr::const_(glue_names::GLUE_SYS_CONS.clone(), vec![lu.clone()]);
    let glue_sys_nil = Expr::const_(glue_names::GLUE_SYS_NIL.clone(), vec![lu.clone()]);
    let glue = Expr::const_(glue_names::GLUE.clone(), vec![lu.clone()]);

    let mut axiom = |name: &str, type_: Expr| -> Result<(), crate::env::EnvError> {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![u.clone()],
            type_,
        })
    };

    // Equiv.{u} (A B : Sort u) : Sort u.
    axiom(
        "Equiv",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(BinderInfo::Default, sort_u.clone(), sort_u.clone()),
        ),
    )?;

    // Equiv.idEquiv.{u} (A : Sort u) : Equiv A A.
    axiom(
        "Equiv.idEquiv",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::apps(equiv.clone(), [Expr::bvar(0), Expr::bvar(0)]),
        ),
    )?;

    // Equiv.fwd.{u} {A B : Sort u} : Equiv A B → A → B  — the forward-map
    // projection of an equivalence. This is the only structure of `Equiv` the
    // univalence computation rule (`coe (ua e) i0 i1 x ↝ Equiv.fwd e x`) needs.
    // de Bruijn under [A, B]: A = BVar1, B = BVar0 at `Equiv A B`; the result
    // `A → B` is `Π(_:A). B` with A = BVar2 (under [A,B,e]) and B = BVar2 (under
    // [A,B,e,_]). SOUNDNESS: `Equiv.fwd` is an opaque value axiom over the opaque
    // `Equiv` former — it asserts nothing about the structure of the type and so,
    // like `Equiv.idEquiv`, never introduces inconsistency (an opaque type with
    // an asserted projection has no eliminator and no relation to other types).
    axiom(
        "Equiv.fwd",
        Expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(), // A
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(), // B
                Expr::arrow(
                    Expr::apps(equiv.clone(), [Expr::bvar(1), Expr::bvar(0)]), // Equiv A B
                    Expr::arrow(Expr::bvar(2), Expr::bvar(2)),                 // A → B
                ),
            ),
        ),
    )?;

    // Equiv.bwd.{u} {A B : Sort u} : Equiv A B → B → A  — the **backward-map**
    // projection of an equivalence (the quasi-inverse `g`). This is the computable
    // fiber-center datum that the general `transp`-over-`Glue` correction consumes:
    // for `b : A` the fiber center of `f` over `b` is `(g b, ε b)`, so its *point*
    // is exactly `Equiv.bwd e b`. Mirrors `Equiv.fwd` (same opaque-projection
    // soundness: an asserted projection over the `Equiv` former introduces no
    // inconsistency; its β-rule projects `g`, which has the exact type `B → A`).
    // de Bruijn under [A,B]: `Equiv A B` = `Equiv (bvar1)(bvar0)`; the result
    // `B → A` is `Π(_:B). A` — at [A,B,e] the domain `B` = bvar1, and inside the
    // arrow at [A,B,e,_] the codomain `A` = bvar3.
    axiom(
        "Equiv.bwd",
        Expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(), // A
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(), // B
                Expr::arrow(
                    Expr::apps(equiv.clone(), [Expr::bvar(1), Expr::bvar(0)]), // Equiv A B
                    Expr::arrow(Expr::bvar(1), Expr::bvar(3)),                 // B → A
                ),
            ),
        ),
    )?;

    // Equiv.mk.{u} {A B : Sort u} (f : A→B) (g : B→A)
    //   (η : (x:A) → Path (λ_:I. A) (g (f x)) x)   -- g ∘ f ~ id_A
    //   (ε : (y:B) → Path (λ_:I. B) (f (g y)) y)   -- f ∘ g ~ id_B
    //   : Equiv A B.
    //
    // This is the **constructor** of `Equiv` as a genuine equivalence record:
    // forward map `f`, backward map `g`, and the two inverse-homotopies `η`/`ε`.
    // It makes `Equiv.fwd` a *computing* first projection
    // (`Equiv.fwd (Equiv.mk f g η ε) ↝ f`, the β-rule in `try_glue_reduction`),
    // which is what lets `transport (ua (Equiv.mk f …)) x ↝ f x` reduce CONCRETELY.
    //
    // SOUNDNESS: `Equiv A B` is now exactly the record
    // `{ f:A→B, g:B→A, η:g∘f~id, ε:f∘g~id }` — a standard structure. Its field
    // types are ordinary, consistent type expressions (Π and cubical `Path`), and
    // the whole record is inhabited (e.g. `A≡B`, `f=g=id`, `η=ε=refl`), so adding
    // the constructor is consistency-preserving. Crucially the constructor demands
    // *real* inverse data: you cannot fabricate `Equiv A B` between
    // logically-inequivalent types (you would need total maps **both** ways plus
    // their coherences), so univalence (`ua`) only ever transports along genuine
    // equivalences. `Equiv.fwd`'s β-rule projects the asserted `f`, which has the
    // exact type `A→B` of `Equiv.fwd e` — the rewrite preserves type.
    //
    // de Bruijn (outermost→innermost binders [A,B,f,g,η,ε]): see the per-line
    // index annotations below; `Path` lines re-bind one extra interval variable.
    let path = |line: Expr, left: Expr, right: Expr| {
        Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(line),
            left: Arc::new(left),
            right: Arc::new(right),
        })
    };
    let equiv_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        sort_u.clone(), // A
        Expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(Expr::bvar(1), Expr::bvar(1)), // f : A → B
                Expr::pi(
                    BinderInfo::Default,
                    Expr::arrow(Expr::bvar(1), Expr::bvar(3)), // g : B → A
                    Expr::pi(
                        BinderInfo::Default,
                        // η : (x:A) → Path (λ_:I. A) (g (f x)) x
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(3), // x : A
                            path(
                                Expr::lam(BinderInfo::Default, i(), Expr::bvar(5)), // λ_:I. A
                                Expr::app(Expr::bvar(1), Expr::app(Expr::bvar(2), Expr::bvar(0))), // g (f x)
                                Expr::bvar(0), // x
                            ),
                        ),
                        Expr::pi(
                            BinderInfo::Default,
                            // ε : (y:B) → Path (λ_:I. B) (f (g y)) y
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::bvar(3), // y : B
                                path(
                                    Expr::lam(BinderInfo::Default, i(), Expr::bvar(5)), // λ_:I. B
                                    Expr::app(
                                        Expr::bvar(3),
                                        Expr::app(Expr::bvar(2), Expr::bvar(0)),
                                    ), // f (g y)
                                    Expr::bvar(0),                                      // y
                                ),
                            ),
                            // result : Equiv A B  (A = BVar5, B = BVar4)
                            Expr::apps(equiv.clone(), [Expr::bvar(5), Expr::bvar(4)]),
                        ),
                    ),
                ),
            ),
        ),
    );
    axiom("Equiv.mk", equiv_mk_ty)?;

    // Equiv.toIsEquiv.{u} {A B : Sort u} (e : Equiv A B) : isEquiv (Equiv.fwd e)
    //   — the **coherence projection** of an equivalence: every `Equiv A B` has a
    // contractible-fibre `isEquiv` witness for its forward map. This is the carried
    // witness for cells whose equivalence is *opaque* (the `ua` cells' genuine `e`,
    // and neutral test equivalences): the residual `transp`-over-`Glue` rule reads
    // the cell's `isEquiv` to obtain the fibre centre, and for an opaque cell that
    // read stays **stuck** (`Equiv.toIsEquiv e a₁` is a neutral spine, so its
    // `.centre.fst` never computes) — so it never produces a wrong value, exactly
    // mirroring how `Equiv.fwd`/`Equiv.bwd` stay stuck on a neutral equivalence.
    //
    // SOUNDNESS: an opaque value axiom over the opaque `Equiv` former. In the
    // intended model `Equiv A B` *is* the type of genuine equivalences, every one
    // of which carries an `isEquiv` for its forward map, so the axiom is
    // interpretable (consistency-preserving) — it asserts no false proposition and,
    // like `Equiv.fwd`/`Equiv.bwd`, has no eliminator that could relate distinct
    // types. de Bruijn under [A,B]: A = BVar1, B = BVar0; `e` = BVar0 under [A,B,e].
    let equiv_fwd = Expr::const_(glue_names::EQUIV_FWD.clone(), vec![lu.clone()]);
    let to_is_equiv_ty = Expr::pi(
        BinderInfo::Implicit,
        sort_u.clone(), // A
        Expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                Expr::apps(equiv.clone(), [Expr::bvar(1), Expr::bvar(0)]), // e : Equiv A B
                // isEquiv (Equiv.fwd A B e) : Sort u.   At [A,B,e]: A=2, B=1, e=0.
                is_equiv_type(
                    lu.clone(),
                    &Expr::bvar(2), // A
                    &Expr::bvar(1), // B
                    &Expr::apps(equiv_fwd, [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]),
                ),
            ),
        ),
    );
    axiom("Equiv.toIsEquiv", to_is_equiv_ty)?;

    // Glue.Sys.{u} (B : Sort u) : Sort u  (opaque type of glue-systems over B).
    axiom(
        "Glue.Sys",
        Expr::pi(BinderInfo::Default, sort_u.clone(), sort_u.clone()),
    )?;

    // Glue.Sys.nil.{u} (B : Sort u) : Glue.Sys B.
    axiom(
        "Glue.Sys.nil",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::app(glue_sys.clone(), Expr::bvar(0)),
        ),
    )?;

    // Glue.Sys.cons.{u} (B:Sort u)(φ:I)(T:Sort u)(e:Equiv T B)
    //   (ie : isEquiv (Equiv.fwd e))(tail:Glue.Sys B) : Glue.Sys B.
    //
    // The fifth field `ie` is the **carried contractible-fibre witness** that the
    // residual `transp`-over-`Glue` rule reads to obtain the fibre centre at the
    // target endpoint (the fix for "Glue cells carry an opaque quasi-inverse, no
    // isEquiv"). For `ua` cells it is supplied opaquely (`Equiv.toIsEquiv`); for
    // `hcomp`-in-universe (`coeEquiv`) cells it is the genuine, *computing*
    // `is_equiv_coe` proof. de Bruijn (innermost = 0): in `e`'s type T=BVar1,B=BVar2;
    // in `ie`'s type T=BVar1,B=BVar3,e=BVar0; `tail`'s type B=BVar4; result B=BVar5.
    let equiv_fwd_for_cell = Expr::const_(glue_names::EQUIV_FWD.clone(), vec![lu.clone()]);
    axiom(
        "Glue.Sys.cons",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                i(), // φ
                Expr::pi(
                    BinderInfo::Default,
                    sort_u.clone(), // T
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::apps(equiv.clone(), [Expr::bvar(0), Expr::bvar(2)]), // e : Equiv T B
                        Expr::pi(
                            BinderInfo::Default,
                            // ie : isEquiv (Equiv.fwd T B e).  At [B,φ,T,e]: T=1,B=3,e=0.
                            is_equiv_type(
                                lu.clone(),
                                &Expr::bvar(1), // T
                                &Expr::bvar(3), // B
                                &Expr::apps(
                                    equiv_fwd_for_cell.clone(),
                                    [Expr::bvar(1), Expr::bvar(3), Expr::bvar(0)],
                                ),
                            ),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::app(glue_sys.clone(), Expr::bvar(4)), // tail : Glue.Sys B
                                Expr::app(glue_sys.clone(), Expr::bvar(5)), // result : Glue.Sys B
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )?;

    // Glue.{u} (B:Sort u)(φ:I)(sys:Glue.Sys B) : Sort u.
    axiom(
        "Glue",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                i(), // φ
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(glue_sys.clone(), Expr::bvar(1)), // sys : Glue.Sys B
                    sort_u.clone(),
                ),
            ),
        ),
    )?;

    // unglue.{u} (B:Sort u)(φ:I)(sys:Glue.Sys B)(g:Glue B φ sys) : B.
    axiom(
        "unglue",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                i(), // φ
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(glue_sys.clone(), Expr::bvar(1)), // sys : Glue.Sys B
                    Expr::pi(
                        BinderInfo::Default,
                        // g : Glue B φ sys  (B=BVar2, φ=BVar1, sys=BVar0)
                        Expr::apps(glue.clone(), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]),
                        Expr::bvar(3), // result : B
                    ),
                ),
            ),
        ),
    )?;

    // glue.{u} (B:Sort u)(T:Sort u)(φ:I)(e:Equiv T B)(ie:isEquiv (Equiv.fwd e))(t:T)(a:B)
    //   : Glue B φ (Glue.Sys.cons B φ T e ie (Glue.Sys.nil B)).
    // Under all 7 binders [B,T,φ,e,ie,t,a]: B=6, T=5, φ=4, e=3, ie=2 (t=1,a=0).
    let glue_result = Expr::apps(
        glue.clone(),
        [
            Expr::bvar(6), // B
            Expr::bvar(4), // φ
            Expr::apps(
                glue_sys_cons,
                [
                    Expr::bvar(6),                          // B
                    Expr::bvar(4),                          // φ
                    Expr::bvar(5),                          // T
                    Expr::bvar(3),                          // e
                    Expr::bvar(2),                          // ie
                    Expr::app(glue_sys_nil, Expr::bvar(6)), // Glue.Sys.nil B
                ],
            ),
        ],
    );
    axiom(
        "glue",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // B
            Expr::pi(
                BinderInfo::Default,
                sort_u.clone(), // T
                Expr::pi(
                    BinderInfo::Default,
                    i(), // φ
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::apps(equiv, [Expr::bvar(1), Expr::bvar(2)]), // e : Equiv T B
                        Expr::pi(
                            BinderInfo::Default,
                            // ie : isEquiv (Equiv.fwd T B e).  At [B,T,φ,e]: T=2,B=3,e=0.
                            is_equiv_type(
                                lu.clone(),
                                &Expr::bvar(2), // T
                                &Expr::bvar(3), // B
                                &Expr::apps(
                                    equiv_fwd_for_cell,
                                    [Expr::bvar(2), Expr::bvar(3), Expr::bvar(0)],
                                ),
                            ),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::bvar(3), // t : T
                                Expr::pi(
                                    BinderInfo::Default,
                                    Expr::bvar(5), // a : B
                                    glue_result,
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )?;

    Ok(())
}

/// Build the **univalence** path `ua e : A = B` (Glue Phase 0–2 soundness
/// anchor):
///
/// ```text
/// ua e := <i> Glue B [ (i=0) ↦ (A, e),  (i=1) ↦ (B, Equiv.idEquiv B) ]
/// ```
///
/// With `e : Equiv A B`, this infers to `Path (λ_. Sort u) A B` (= `A = B`):
/// `infer(<i> body) = Path (λ i. infer(body[i])) body[i0] body[i1]`, where
/// `infer(body[i]) = Sort u` (constant) so the family is `λ_. Sort u`, and the
/// boundary rule gives `body[i0] = Glue B [⊤↦(A,e), ⊥↦…] ↝ A`,
/// `body[i1] ↝ B`.
///
/// `level` is the universe of `A`/`B` (`Sort u`). Like [`path_compose`], the
/// inputs `a_ty`, `b_ty`, `equiv` are assumed **closed** (no loose BVar 0); the
/// only term that references the outer interval binder `<i>` (= `BVar(0)`) is the
/// cell faces.
// Not yet wired to a production caller (the elaborator surface for `ua` is future
// work); exercised by the Glue / univalence soundness tests.
#[allow(dead_code)]
pub(crate) fn glue_ua(a_ty: &Expr, b_ty: &Expr, equiv: &Expr, level: Level) -> Expr {
    let levels = vec![level.clone()];
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), [x, y]);

    let glue = Expr::const_(glue_names::GLUE.clone(), levels.clone());
    let glue_sys_cons = Expr::const_(glue_names::GLUE_SYS_CONS.clone(), levels.clone());
    let glue_sys_nil = Expr::const_(glue_names::GLUE_SYS_NIL.clone(), levels.clone());
    let id_equiv = Expr::const_(glue_names::EQUIV_ID.clone(), levels.clone());

    // i = BVar(0) under the outer `<i>`.
    let face_i0 = cofib_eq0(Expr::bvar(0)); // (i=0)
    let face_i1 = cofib_eq1(Expr::bvar(0)); // (i=1)
    let phi_overall = cofib_or(face_i0.clone(), face_i1.clone());

    // [(i=1) ↦ (B, idEquiv B, idIsEquiv B)] ∷ nil
    //   — Glue.Sys.cons args = (B, φ, T, e, ie, tail). The `(i=1)` cell's equiv is
    //   the identity, so its carried `isEquiv` is the genuine, computing
    //   `id_is_equiv` (defeq to `isEquiv (Equiv.fwd (idEquiv B))` since
    //   `Equiv.fwd (idEquiv B) ↝ λz.z`).
    let nil = Expr::app(glue_sys_nil, b_ty.clone());
    let cell_i1 = Expr::apps(
        glue_sys_cons.clone(),
        [
            b_ty.clone(),                      // B
            face_i1,                           // φ = (i=1)
            b_ty.clone(),                      // T = B
            Expr::app(id_equiv, b_ty.clone()), // e = idEquiv B : Equiv B B
            id_is_equiv(level.clone(), b_ty),  // ie : isEquiv (λz.z)
            nil,
        ],
    );
    // (i=0) ↦ (A, e, Equiv.toIsEquiv A B e) ∷ cell_i1. The univalence cell's equiv
    // is **opaque** (the user's `e`), so its carried `isEquiv` is the opaque
    // coherence projection `Equiv.toIsEquiv` — the residual rule never *reads* it
    // (the `ua` line is a ⊤-cell case at both endpoints), and were it read it would
    // stay stuck (sound), never producing a wrong value.
    let to_is_equiv = Expr::const_(glue_names::EQUIV_TO_IS_EQUIV.clone(), levels.clone());
    let cell_i0 = Expr::apps(
        glue_sys_cons,
        [
            b_ty.clone(),                                                         // B
            face_i0,                                                              // φ = (i=0)
            a_ty.clone(),                                                         // T = A
            equiv.clone(),                                                        // e : Equiv A B
            Expr::apps(to_is_equiv, [a_ty.clone(), b_ty.clone(), equiv.clone()]), // ie
            cell_i1,
        ],
    );

    let glue_ty = Expr::apps(glue, [b_ty.clone(), phi_overall, cell_i0]);
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(glue_ty),
    })
}

/// Build the **homogeneous Kan filler** `hfill` (Kan-filling deliverable 1).
///
/// `hfill` is *not* a new primitive — it is an ordinary `hcomp` over the
/// interval connection `I.min` (`∧`). For a single user face `φ` with tube
/// `u : I → A` and floor `base : A`, and a fill parameter `r : I`:
///
/// ```text
/// hfill {A} [φ ↦ u] base r
///   :=  hcomp {A} [ φ ↦ (λ j. u (r ∧ j)),  (r = 0) ↦ (λ _. base) ] base
/// ```
///
/// which has type `A` and interpolates the floor with the full composite:
/// * `hfill {A} [φ↦u] base i0 ≡ base` — at `r = i0` the extra cell's face
///   `(i0 = 0) ⇓ ⊤` fires the on-a-true-face `hcomp` rule, whose lid is
///   `(λ _. base) i1 ≡ base` (when `φ` is not *also* total — i.e. away from the
///   boundary where the coherence forces `u i0 ≡ base` anyway);
/// * `hfill {A} [⊤↦u] base i1 ≡ hcomp {A} [⊤↦u] base` — at `r = i1` the extra
///   cell's face `(i1 = 0) ⇓ ⊥` drops out and `r ∧ j ↝ j` collapses the φ tube
///   back to `u`, so on a total `φ` both sides reduce to `u i1`.
///
/// ## de Bruijn discipline
///
/// `hfill` returns a *plain* term of type `A` (no outer interval binder of its
/// own — unlike [`path_compose`], which is wrapped in `<i>`). The inputs `phi`,
/// `u`, `base`, `r` are valid in the caller's context. The only binders this
/// helper introduces are the two ordinary tube functions `λ j:I. …` (a `Lam`,
/// **not** a path-lam), so inside a tube `j = BVar(0)` and the captured `u`/`r`
/// (resp. `base`) are `lift`ed by one (a no-op when they are closed at the call
/// site, defensively correct otherwise). The cell faces `φ` / `(r = 0)` and the
/// `hcomp` `phi` field carry no binder of their own, so `r`/`phi` appear there
/// unshifted.
///
/// SOUNDNESS: `hfill` is *defined* as an `hcomp`, so it is exactly as sound as
/// the existing [`Self::try_hcomp_reduction`] — it introduces no new reduction
/// rule and no new typing rule. The two endpoint facts are not asserted; they
/// **compute** through the on-a-true-face / `I.min` rules already in the kernel.
// Not yet wired to a production caller (the elaborator surface for `hfill` is
// future work); exercised by the Kan-filling soundness tests.
#[allow(dead_code)]
pub(crate) fn hfill(
    a_type: &Expr,
    level: Level,
    phi: &Expr,
    u: &Expr,
    base: &Expr,
    r: &Expr,
) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_or =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), [x, y]);
    let i_min =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MIN.clone(), vec![]), [x, y]);

    let levels = vec![level];
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), levels.clone()),
            [a_type.clone(), face, head, tail],
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), levels.clone()),
        a_type.clone(),
    );

    // φ tube: `λ j:I. u (r ∧ j)`. Inside the `λ j`, j = BVar(0); `u`/`r` are
    // lifted past the introduced binder (no-op when closed).
    let branch_phi = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(u.lift(1), i_min(r.lift(1), Expr::bvar(0))),
    );
    // (r=0) tube: `λ _:I. base` (constant in j); `base` lifted past the binder.
    let branch_r0 = Expr::lam(BinderInfo::Default, interval(), base.lift(1));

    let face_r0 = cofib_eq0(r.clone());

    // System: `[ φ ↦ branch_phi,  (r=0) ↦ branch_r0 ]`.
    let system = sys_cons(
        phi.clone(),
        branch_phi,
        sys_cons(face_r0.clone(), branch_r0, sys_nil),
    );
    // Overall extent `φ ∨ (r=0)` (used only by the empty-extent `hcomp` rule;
    // the per-cell faces are read from the `System.cons` cells).
    let phi_field = cofib_or(phi.clone(), face_r0);

    Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a_type.clone()),
        phi: Arc::new(phi_field),
        u: Arc::new(system),
        base: Arc::new(base.clone()),
    })
}

/// Build `coeEquiv L : Equiv (L i1) (L i0)` — **coercion along a line is an
/// equivalence** (Kan-filling deliverable 2; the cubical `isEquivTransport` /
/// `transpEquiv`). This is the `e_T` that the `hcomp`-in-`U` → `Glue` reduction
/// needs (an equivalence between the line's endpoints).
///
/// With `L : I → Sort u` a *line of types*:
///
/// ```text
/// f := λ x. coe L i1 i0 x   : L i1 → L i0     -- coe backward (the "forward" map)
/// g := λ y. coe L i0 i1 y   : L i0 → L i1     -- coe forward
/// η x := <k> coe L k  i1 (coe L i1 k  x)      : Path (λ_.L i1) (g (f x)) x
/// ε y := <k> coe L (~k) i0 (coe L i0 (~k) y)  : Path (λ_.L i0) (f (g y)) y
/// coeEquiv L := Equiv.mk (L i1) (L i0) f g η ε
/// ```
///
/// ## How η / ε are discharged (the crux)
///
/// The round-trip homotopies are built from the **coe-filler** — the native
/// generalized coercion `coe L r s` with a *variable* endpoint, which is exactly
/// the filling apparatus the `Equiv.mk` coherence fields require (no separate
/// `hfill` is needed because `coe^{r→s}` already fills a heterogeneous line).
///
/// For η, `coe L i1 k x : L k` is the coe-filler from `x` (at `k = i1`) down to
/// `f x = coe L i1 i0 x` (at `k = i0`); transporting each point of that filler
/// back up with `coe L k i1 : L k → L i1` yields a path **in the fixed type
/// `L i1`**:
/// * at `k = i1`: `coe L i1 i1 (coe L i1 i1 x) ≡ x` (the degenerate `coe` rule,
///   twice) — the right endpoint;
/// * at `k = i0`: `coe L i0 i1 (coe L i1 i0 x)` which is **literally** `g (f x)`
///   after β — the left endpoint.
/// `ε` is the mirror with the source line reversed (`~k`), so the round-trip
/// `f (g y)` lands at `k = i0` and the identity `y` at `k = i1`. Both bodies have
/// type `L i1` / `L i0` at *every* interval point, so each path family is the
/// **constant** `λ_. L i1` / `λ_. L i0` (a homogeneous path), as `Equiv.mk`
/// demands.
///
/// ## Constant-line degeneration (the key sanity check)
///
/// For `L = λ_. A` every `coe` collapses by the constant-line rule, so
/// `f ≡ g ≡ id_A`, `η ≡ ε ≡ refl`, and the forward map
/// `Equiv.fwd (coeEquiv (λ_.A)) ≡ Equiv.fwd (Equiv.idEquiv A) ≡ λx. x` — i.e.
/// `coeEquiv` degenerates to the identity equivalence, confirming it is the
/// *right* equivalence (the documented regularity rule).
///
/// `level` is the universe of `L`'s values (`Sort u`). Like the other helpers,
/// `line` is assumed **closed** (no loose `BVar`): the `coe` `ty` fields and the
/// `App(L, i0/i1)` endpoints reference it directly under the introduced binders.
///
/// SOUNDNESS: this is a *closed term* assembled only from the existing `coe`
/// primitive, the interval reversal `~`, `CubicalPathLam`, and `Equiv.mk` — it
/// adds **no** reduction rule and **no** axiom. It type-checks as `Equiv` exactly
/// because the endpoint reductions above are the kernel's own degenerate/`I.neg`
/// `coe` rules; the interiors stay (soundly) stuck for a generic line.
// Not yet wired to a production caller (the elaborator surface for `coeEquiv` is
// future work); exercised by the Kan-filling soundness tests.
#[allow(dead_code)]
pub(crate) fn coe_equiv(line: &Expr, level: Level) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let i1 = || Expr::from_kind(ExprKind::CubicalI1);
    let app_l = |arg: Expr| Expr::app(line.clone(), arg);
    let coe = |r: Expr, s: Expr, base: Expr| {
        Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(line.clone()),
            r: Arc::new(r),
            s: Arc::new(s),
            base: Arc::new(base),
        })
    };
    let i_neg = |x: Expr| Expr::app(Expr::const_(conn_names::I_NEG.clone(), vec![]), x);

    let a = app_l(i1()); // A = L i1
    let b = app_l(i0()); // B = L i0

    // f : A → B = λ (x:A). coe L i1 i0 x.   (under λx: x = BVar 0)
    let f = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        coe(i1(), i0(), Expr::bvar(0)),
    );
    // g : B → A = λ (y:B). coe L i0 i1 y.
    let g = Expr::lam(
        BinderInfo::Default,
        b.clone(),
        coe(i0(), i1(), Expr::bvar(0)),
    );

    // η : (x:A) → Path (λ_.A) (g (f x)) x,  η x := <k> coe L k i1 (coe L i1 k x).
    // Under λx then <k>: k = BVar(0), x = BVar(1).
    let eta_inner = coe(i1(), Expr::bvar(0), Expr::bvar(1)); // coe L i1 k x
    let eta_body = coe(Expr::bvar(0), i1(), eta_inner); // coe L k i1 (…)
    let eta = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(eta_body),
        }),
    );

    // ε : (y:B) → Path (λ_.B) (f (g y)) y,  ε y := <k> coe L (~k) i0 (coe L i0 (~k) y).
    // Under λy then <k>: k = BVar(0), y = BVar(1); ~k = I.neg (BVar 0).
    let eps_inner = coe(i0(), i_neg(Expr::bvar(0)), Expr::bvar(1)); // coe L i0 (~k) y
    let eps_body = coe(i_neg(Expr::bvar(0)), i0(), eps_inner); // coe L (~k) i0 (…)
    let eps = Expr::lam(
        BinderInfo::Default,
        b.clone(),
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(eps_body),
        }),
    );

    Expr::apps(
        Expr::const_(glue_names::EQUIV_MK.clone(), vec![level]),
        [a, b, f, g, eta, eps],
    )
}

/// Register the reserved **dependent-sum (`Σ`)** constants (see [`sigma_names`])
/// into a **Cubical-mode** environment, with the type-valued axiom types that make
/// the Expr-encoding genuinely well-typed (`Sigma A B : Sort u`,
/// `Sigma.mk … : Sigma A B`, the dependent eliminator `Sigma.elim`). This lets the
/// existing inference / certificate machinery accept the cubical `isEquiv` /
/// `isContr` / `fiber` constructions unchanged (they are plain `Const`/`App`
/// spines), exactly as for [`register_glue_axioms`].
///
/// SOUNDNESS of the axiom set: `Sigma` is the standard dependent sum, `Sigma.mk`
/// its pairing constructor, and `Sigma.elim` its dependent eliminator. The genuine
/// Σ-type in the cubical model satisfies *exactly* this eliminator
/// (`elim M m (mk a b) = m a b`), so asserting former + constructor + eliminator as
/// axioms is consistency-preserving — it is interpretable by the actual dependent
/// sum. We deliberately do **not** add the iota computation rule
/// (`Sigma.elim … (Sigma.mk …) ↝ m …`): omitting it only makes the theory *weaker*
/// (never unsound), and the cubical `isEquiv` layer never needs it — it only ever
/// applies `Sigma.elim` to a *variable* (when contracting an abstract fiber point),
/// never to a literal `Sigma.mk`. This mirrors the opaque-`Equiv` axiomatization
/// (`Equiv.mk` + `Equiv.fwd`): an asserted constructor + eliminator over a
/// consistent former introduces no inconsistency.
///
/// Idempotent-ish: register once per environment. Returns the first registration
/// error if any.
// Not yet wired to a production caller (cubical environments are configured by
// tests for now); exercised by the `isEquiv` / contractible-fiber soundness tests.
#[allow(dead_code)]
pub(crate) fn register_sigma_axioms(env: &mut Environment) -> Result<(), crate::env::EnvError> {
    let u = Name::from_string("u");
    let lu = Level::param(u.clone());
    let sort_u = Expr::sort(lu.clone());
    let sigma = Expr::const_(sigma_names::SIGMA.clone(), vec![lu.clone()]);
    let sigma_mk = Expr::const_(sigma_names::SIGMA_MK.clone(), vec![lu.clone()]);

    // Idempotent: a cubical env may register Sigma both directly *and* via
    // [`register_glue_axioms`] (which now depends on `Sigma` for the carried-
    // `isEquiv` cell witness). `add_decl_if_absent` makes either order, or both,
    // a no-op the second time — never a `DuplicateName`.
    let mut axiom = |name: &str, type_: Expr| -> Result<(), crate::env::EnvError> {
        env.add_decl_if_absent(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![u.clone()],
            type_,
        })
    };

    // Sigma.{u} (A : Sort u) (B : A → Sort u) : Sort u.
    // de Bruijn: inside `B`'s domain `A` = BVar(0).
    axiom(
        "Sigma",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // A
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(Expr::bvar(0), sort_u.clone()), // B : A → Sort u
                sort_u.clone(),
            ),
        ),
    )?;

    // Sigma.mk.{u} (A : Sort u) (B : A → Sort u) (a : A) (b : B a) : Sigma A B.
    // de Bruijn under [A,B,a,b]: A=3, B=2, a=1, b=0 at the result.
    axiom(
        "Sigma.mk",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // A
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(Expr::bvar(0), sort_u.clone()), // B : A → Sort u
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // a : A
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(Expr::bvar(1), Expr::bvar(0)), // b : B a
                        Expr::apps(sigma.clone(), [Expr::bvar(3), Expr::bvar(2)]), // Sigma A B
                    ),
                ),
            ),
        ),
    )?;

    // Sigma.elim.{u} (A)(B)(M : Sigma A B → Sort u)
    //   (m : (a:A) → (b:B a) → M (Sigma.mk A B a b)) (p : Sigma A B) : M p.
    // The minor's type under [A,B,M]: A=2, B=1, M=0; under [A,B,M,a]: B=2, a=0;
    // under [A,B,M,a,b]: M=2, A=4, B=3, a=1, b=0.
    let minor_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(2), // a : A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(2), Expr::bvar(0)), // b : B a
            Expr::app(
                Expr::bvar(2), // M
                Expr::apps(
                    sigma_mk.clone(),
                    [Expr::bvar(4), Expr::bvar(3), Expr::bvar(1), Expr::bvar(0)], // Sigma.mk A B a b
                ),
            ),
        ),
    );
    axiom(
        "Sigma.elim",
        Expr::pi(
            BinderInfo::Default,
            sort_u.clone(), // A
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(Expr::bvar(0), sort_u.clone()), // B : A → Sort u
                Expr::pi(
                    BinderInfo::Default,
                    // M : Sigma A B → Sort u   (A=1, B=0)
                    Expr::arrow(
                        Expr::apps(sigma.clone(), [Expr::bvar(1), Expr::bvar(0)]),
                        sort_u.clone(),
                    ),
                    Expr::pi(
                        BinderInfo::Default,
                        minor_ty, // m
                        Expr::pi(
                            BinderInfo::Default,
                            // p : Sigma A B   (under [A,B,M,m]: A=3, B=2)
                            Expr::apps(sigma.clone(), [Expr::bvar(3), Expr::bvar(2)]),
                            // result : M p   (under [A,B,M,m,p]: M=2, p=0)
                            Expr::app(Expr::bvar(2), Expr::bvar(0)),
                        ),
                    ),
                ),
            ),
        ),
    )?;

    Ok(())
}

// ── `isEquiv` (contractible-fiber) constructions ────────────────────────────────
//
// All builders below emit plain kernel `Expr`s over the reserved `Sigma.*` axioms
// (and the existing `coe`/`Path`/`I.*` primitives). They follow the established
// helper convention (`coe_equiv`, `path_compose`, `glue_ua`): inputs are valid in
// the caller's context, every introduced binder `lift`s the outer terms by one, and
// the result is a closed-up term. SOUNDNESS: these are *constructions*, not new
// reduction rules — the only trusted-surface additions are the Σ axioms above.

/// `Path (λ_:I. t) left right` — the **homogeneous** path type in `t`. `t`,
/// `left`, `right` are valid in the current context; `t` crosses the introduced
/// interval binder (so it is `lift`ed by one inside the family).
#[allow(dead_code)]
fn path_homog(t: &Expr, left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::CubicalInterval),
            t.lift(1),
        )),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}

/// `Σ (a:A). B` — the encoded dependent sum `apps(Sigma.{level}, [A, B])`.
#[allow(dead_code)]
pub(crate) fn sigma_type(level: Level, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(sigma_names::SIGMA.clone(), vec![level]),
        [a.clone(), b.clone()],
    )
}

/// `Sigma.mk.{level} A B fst snd` — the encoded dependent pair.
#[allow(dead_code)]
pub(crate) fn sigma_mk(level: Level, a: &Expr, b: &Expr, fst: Expr, snd: Expr) -> Expr {
    Expr::apps(
        Expr::const_(sigma_names::SIGMA_MK.clone(), vec![level]),
        [a.clone(), b.clone(), fst, snd],
    )
}

/// `p.fst : A` — the **first projection** of a dependent pair `p : Σ (a:A). B`,
/// built as `Sigma.elim A B (λ_:Σ A B. A) (λ (a:A)(b:B a). a) p` (a constant
/// motive, so no Σ-iota is needed; on a literal `Sigma.mk` it computes via
/// [`TypeChecker::try_sigma_reduction`], on a neutral pair it stays soundly
/// stuck). `a` (= A), `b` (= B), `p` are valid in the current context; `level` is
/// the universe of the Σ. Used by the directed Segal layer to take the centre of
/// a contractible composite type and then its composite arrow.
#[allow(dead_code)]
pub(crate) fn sigma_fst(level: Level, a: &Expr, b: &Expr, p: &Expr) -> Expr {
    // M = λ (_ : Σ A B). A   (A lifted past the motive binder).
    let motive = Expr::lam(
        BinderInfo::Default,
        sigma_type(level.clone(), a, b),
        a.lift(1),
    );
    // m = λ (fst:A). λ (snd : B fst). fst.   Under [fst,snd]: fst=BVar1.
    let minor = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(b.lift(1), Expr::bvar(0)), // B fst
            Expr::bvar(1),                       // fst
        ),
    );
    Expr::apps(
        Expr::const_(sigma_names::SIGMA_ELIM.clone(), vec![level]),
        [a.clone(), b.clone(), motive, minor, p.clone()],
    )
}

/// The `fiber`'s Σ second-component family `λ (x:A). Path (λ_.B) (f x) y`.
/// `a`, `b`, `f`, `y` are valid in the current context.
#[allow(dead_code)]
fn fiber_bfam(a: &Expr, b: &Expr, f: &Expr, y: &Expr) -> Expr {
    // Under `λ (x:A)` the bound `x` is BVar(0); the captured `a`/`b`/`f`/`y` are
    // lifted by one.
    Expr::lam(
        BinderInfo::Default,
        a.clone(),
        path_homog(
            &b.lift(1),
            Expr::app(f.lift(1), Expr::bvar(0)), // f x
            y.lift(1),                           // y
        ),
    )
}

/// `fiber f y := Σ (x:A). Path (λ_.B) (f x) y` for `f : A → B` and `y : B`.
/// `a` (= A), `b` (= B), `f`, `y` are valid in the current context; `level` is the
/// common universe of `A`/`B`.
#[allow(dead_code)]
pub(crate) fn fiber_type(level: Level, a: &Expr, b: &Expr, f: &Expr, y: &Expr) -> Expr {
    sigma_type(level.clone(), a, &fiber_bfam(a, b, f, y))
}

/// `isContr F := Σ (c:F). (x:F) → Path (λ_.F) c x` — `F` is contractible (a center
/// `c` with a path to every point). `fib` (= F) is valid in the current context.
#[allow(dead_code)]
pub(crate) fn is_contr_type(level: Level, fib: &Expr) -> Expr {
    // B = λ (c:F). Π (x:F). Path (λ_.F) c x.  Under `λ c` then `Π x`: c=BVar(1),
    // x=BVar(0); `F` is lifted by the two binders (and once more inside `path_homog`).
    let b = Expr::lam(
        BinderInfo::Default,
        fib.clone(),
        Expr::pi(
            BinderInfo::Default,
            fib.lift(1),
            path_homog(&fib.lift(2), Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    sigma_type(level, fib, &b)
}

/// `isEquiv f := (y:B) → isContr (fiber f y)` — the **contractible-fiber**
/// definition of "f is an equivalence". `a` (= A), `b` (= B), `f` are valid in the
/// current context; `level` is the common universe of `A`/`B`.
#[allow(dead_code)]
pub(crate) fn is_equiv_type(level: Level, a: &Expr, b: &Expr, f: &Expr) -> Expr {
    // Under `Π (y:B)` the bound `y` is BVar(0); `a`/`b`/`f` lift by one.
    let fib = fiber_type(
        level.clone(),
        &a.lift(1),
        &b.lift(1),
        &f.lift(1),
        &Expr::bvar(0),
    );
    Expr::pi(BinderInfo::Default, b.clone(), is_contr_type(level, &fib))
}

/// `idIsEquiv A : isEquiv (λ x. x)` — **the identity map has contractible fibers**
/// (the cubical `isContrSingl`/co-singleton contractibility). `a` (= A) must be
/// **closed**; `level` is the universe of `A`.
///
/// For each `y : A` the fiber `fiber id y = Σ (x:A). Path A x y` is contracted to
/// the center `(y, refl y)`; an arbitrary point `(x, q)` (with `q : x ≡ y`) is
/// connected to the center by
///
/// ```text
/// <i> (q @ (~i),  <j> q @ (~i ∨ j))   : Path (fiber id y) (y, refl y) (x, q)
/// ```
///
/// whose two endpoints **compute** to the center and to `(x, q)` via the existing
/// kernel rules — the neutral path-endpoint rule (`q @ i0 ≡ x`, `q @ i1 ≡ y`,
/// read off `q`'s `Path A x y` type), the De Morgan connections (`~i0↝i1`,
/// `i1 ∨ j ↝ i1`, `i0 ∨ j ↝ j`), and path-η (`<j> q@j ≡ q`). The contraction is
/// discharged with `Sigma.elim` applied to the abstract fiber point (no iota rule
/// needed).
///
/// SOUNDNESS: a genuine proof term assembled from `Sigma.mk`/`Sigma.elim`, `coe`-free
/// path machinery, and the interval lattice — no `sorry`, no axiomatized witness.
#[allow(dead_code, non_snake_case)]
pub(crate) fn id_is_equiv(level: Level, a: &Expr) -> Expr {
    let i_neg = |x: Expr| Expr::app(Expr::const_(conn_names::I_NEG.clone(), vec![]), x);
    let i_max =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MAX.clone(), vec![]), [x, y]);
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let path_lam = |body: Expr| {
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(body),
        })
    };

    // Built under `λ (y:A)` — y = BVar(0). `a` and `id_a` are closed.
    let id_a = Expr::lam(BinderInfo::Default, a.clone(), Expr::bvar(0)); // λ z. z
    let y = Expr::bvar(0);

    // Fib = fiber id y = Σ (x:A). Path (λ_.A) (id x) y ;  Bfam its Σ family.
    let bfam_fib = fiber_bfam(a, a, &id_a, &y);
    let fib = sigma_type(level.clone(), a, &bfam_fib);

    // isContr's Σ family  Bfib = λ (c:Fib). Π (x:Fib). Path (λ_.Fib) c x.
    let bfib = Expr::lam(
        BinderInfo::Default,
        fib.clone(),
        Expr::pi(
            BinderInfo::Default,
            fib.lift(1),
            path_homog(&fib.lift(2), Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    // center = (y, refl y) : Fib.   refl y = <_> y (y crosses the path binder).
    let refl_y = path_lam(y.lift(1));
    let center = sigma_mk(level.clone(), a, &bfam_fib, y.clone(), refl_y);

    // contraction = λ (w:Fib). Sigma.elim A Bfam Motive Minor w
    //   : Π (w:Fib). Path (λ_.Fib) center w.
    //
    // Depth at the Minor's deepest interior, context (outer→inner) [y,w,x,q,i]:
    //   i=0, q=1, x=2, w=3, y=4.  `bfam_fib`/`center`/`fib` are anchored at [y]
    //   (y=BVar0), so they lift by the number of binders introduced after `λ y`.
    let minor_body_i = {
        // <i> Sigma.mk A Bfam (q @ ~i) (<j> q @ (~i ∨ j))
        let fst = path_app(Expr::bvar(1), i_neg(Expr::bvar(0))); // q @ ~i
                                                                 // inside `<j>`: context [y,w,x,q,i,j] ⇒ j=0, i=1, q=2.
        let snd = path_lam(path_app(
            Expr::bvar(2),
            i_max(i_neg(Expr::bvar(1)), Expr::bvar(0)),
        )); // <j> q @ (~i ∨ j)
        path_lam(sigma_mk(level.clone(), a, &bfam_fib.lift(4), fst, snd))
    };
    let minor = {
        // λ (x:A). λ (q : Path (λ_.A) (id x) y). minor_body_i
        // q's domain at [y,w,x]: x=0, y=2.
        let q_dom = path_homog(a, Expr::app(id_a.clone(), Expr::bvar(0)), Expr::bvar(2));
        Expr::lam(
            BinderInfo::Default,
            a.clone(),
            Expr::lam(BinderInfo::Default, q_dom, minor_body_i),
        )
    };
    let contraction = {
        // Motive = λ (w':Fib). Path (λ_.Fib) center w'.  At [y,w,w']: w'=0.
        let motive = Expr::lam(
            BinderInfo::Default,
            fib.lift(1),
            path_homog(&fib.lift(2), center.lift(2), Expr::bvar(0)),
        );
        let elim = Expr::apps(
            Expr::const_(sigma_names::SIGMA_ELIM.clone(), vec![level.clone()]),
            [
                a.lift(1),
                bfam_fib.lift(1),
                motive,
                minor,
                Expr::bvar(0), // w
            ],
        );
        Expr::lam(BinderInfo::Default, fib.clone(), elim)
    };

    // isContr (fiber id y) = Sigma.mk Fib Bfib center contraction.
    let is_contr = sigma_mk(level, &fib, &bfib, center, contraction);
    Expr::lam(BinderInfo::Default, a.clone(), is_contr)
}

/// `isEquivCoe L : isEquiv (λ x. coe L i1 i0 x)` — **coercion along a line has
/// contractible fibers** (the cubical `isEquivTransport`). `line` (= `L : I → Sort
/// u`) is **closed**; `level` is `u`.
///
/// The fiber-contraction is discharged by **transport** (the agda/cubical recipe):
/// the family `λ i. isEquiv (λ x. coe L i1 i x)` connects `isEquiv (id_{L i1})` (at
/// `i = i1`, since `coe L i1 i1 x ≡ x`) to `isEquiv (λ x. coe L i1 i0 x)` (at
/// `i = i0`), so
///
/// ```text
/// isEquivCoe L := coe (λ i. isEquiv (λ x. coe L i1 i x)) i1 i0 (idIsEquiv (L i1)).
/// ```
///
/// This type-checks to exactly `isEquiv (λ x. coe L i1 i0 x)`: the `coe` result
/// type is the line at `i0`, and the base `idIsEquiv (L i1)` matches the line at
/// `i1` because `coe L i1 i1 x ≡ x` (the degenerate-`coe` rule) makes
/// `λ x. coe L i1 i1 x ≡ λ x. x`.
///
/// SOUNDNESS: a genuine `coe` of the genuine identity-is-equiv proof
/// ([`id_is_equiv`]) — no shortcut, no axiomatized `isEquiv`. The fiber
/// contraction is *carried by the transport*, exactly as in cubical Agda's
/// `isEquivTransport`.
#[allow(dead_code, non_snake_case)]
pub(crate) fn is_equiv_coe(level: Level, line: &Expr) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let i1 = || Expr::from_kind(ExprKind::CubicalI1);

    // base = idIsEquiv (L i1)  (L i1 is closed).
    let a = Expr::app(line.clone(), i1());
    let base = id_is_equiv(level.clone(), &a);

    // line  M = λ i. isEquiv (L i1) (L i) (λ x. coe L i1 i x).
    // Under `λ i` (i=BVar0): `line` lifts by one for `M`'s body, by two under `λ x`.
    let line1 = line.lift(1);
    let a_i = Expr::app(line1.clone(), i1()); // L i1
    let b_i = Expr::app(line1, Expr::bvar(0)); // L i
    let f = Expr::lam(
        BinderInfo::Default,
        a_i.clone(),
        Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(line.lift(2)),
            r: Arc::new(i1()),
            s: Arc::new(Expr::bvar(1)),    // i
            base: Arc::new(Expr::bvar(0)), // x
        }),
    );
    let m_line = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        is_equiv_type(level.clone(), &a_i, &b_i, &f),
    );

    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(m_line),
        r: Arc::new(i1()),
        s: Arc::new(i0()),
        base: Arc::new(base),
    })
}

/// `coeEquivIsEquiv L : Σ (f : L i1 → L i0). isEquiv f` — package the forward coe
/// map with its contractible-fiber proof (the shape a future Glue-`comp` correction
/// consumes). `line` (= `L`) is **closed**; `level` is `L`'s value universe.
///
/// SOUNDNESS: the pair `(λ x. coe L i1 i0 x, isEquivCoe L)` — both components are
/// genuine terms ([`is_equiv_coe`]); nothing is asserted.
#[allow(dead_code, non_snake_case)]
pub(crate) fn coe_equiv_is_equiv(level: Level, line: &Expr) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let i1 = || Expr::from_kind(ExprKind::CubicalI1);

    let a = Expr::app(line.clone(), i1()); // L i1
    let b = Expr::app(line.clone(), i0()); // L i0
    let fn_ty = Expr::arrow(a.clone(), b.lift(1)); // L i1 → L i0

    // f = λ (x:L i1). coe L i1 i0 x.
    let f = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(line.lift(1)),
            r: Arc::new(i1()),
            s: Arc::new(i0()),
            base: Arc::new(Expr::bvar(0)),
        }),
    );

    // B-family = λ (g : L i1 → L i0). isEquiv g.   Under `λ g`: a/b lift by one.
    let bfam = Expr::lam(
        BinderInfo::Default,
        fn_ty.clone(),
        is_equiv_type(level.clone(), &a.lift(1), &b.lift(1), &Expr::bvar(0)),
    );

    sigma_mk(level.clone(), &fn_ty, &bfam, f, is_equiv_coe(level, line))
}

// ── h-level library (`isProp` / `isSet`) ────────────────────────────────────────
//
// The Rung-1 univalent h-level layer, built on the existing `isContr` (Σ-encoded)
// and the cubical path machinery. All builders emit plain kernel `Expr`s; the only
// trusted-surface additions remain the Σ axioms ([`register_sigma_axioms`]). Every
// proof term below is discharged by genuine `hcomp`/`Path`/`Sigma.elim` machinery —
// no `sorry`, no axiomatized h-level witness — and so is subject to the enforced
// `validate_hcomp_cap` side condition.

/// `isProp A := (x y : A) → Path (λ_.A) x y` — "A is a proposition" (any two
/// elements are equal). `a` (= A) is valid in the current context; `is_prop_type`
/// is lift-correct for any such `a` (it `lift`s `a` once/twice for the deeper
/// occurrences), so it also nests under [`is_set_type`].
#[allow(dead_code)]
pub(crate) fn is_prop_type(a: &Expr) -> Expr {
    // Π (x:A). Π (y:A). Path (λ_.A) x y.  Under [x,y]: x=BVar1, y=BVar0.
    Expr::pi(
        BinderInfo::Default,
        a.clone(),
        Expr::pi(
            BinderInfo::Default,
            a.lift(1),
            path_homog(&a.lift(2), Expr::bvar(1), Expr::bvar(0)),
        ),
    )
}

/// `isSet A := (x y : A) → isProp (Path (λ_.A) x y)` — "A is a set" (its path
/// spaces are propositions). `a` (= A) is valid in the current context.
#[allow(dead_code)]
pub(crate) fn is_set_type(a: &Expr) -> Expr {
    // Π (x:A). Π (y:A). isProp (Path (λ_.A) x y).  The inner path type is valid
    // under [x,y] (x=BVar1, y=BVar0); `is_prop_type` lifts it for its own binders.
    let path_xy = path_homog(&a.lift(2), Expr::bvar(1), Expr::bvar(0));
    Expr::pi(
        BinderInfo::Default,
        a.clone(),
        Expr::pi(BinderInfo::Default, a.lift(1), is_prop_type(&path_xy)),
    )
}

/// The `isContr` Σ second-component family `λ (c:F). Π (z:F). Path (λ_.F) c z`
/// (the "center connects to every point" predicate). `fib` (= F) valid in the
/// current context. Matches the `bfib` built inside [`id_is_equiv`].
#[allow(dead_code)]
pub(crate) fn is_contr_bfam(fib: &Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        fib.clone(),
        Expr::pi(
            BinderInfo::Default,
            fib.lift(1),
            path_homog(&fib.lift(2), Expr::bvar(1), Expr::bvar(0)),
        ),
    )
}

/// `isContr→isProp : isContr A → isProp A` — a contractible type is a proposition.
///
/// ```text
/// isContr→isProp (c, h) x y := <i> hcomp {A} [ (i=0) ↦ λ k. (h x) @ k,
///                                              (i=1) ↦ λ k. (h y) @ k ] c
/// ```
///
/// With `h x : c ≡ x` and `h y : c ≡ y`, the square's `(i=0)` wall runs `c ⇝ x`
/// and the `(i=1)` wall runs `c ⇝ y`, so the lid is a path `x ≡ y`. The center `c`
/// and contraction `h` are projected with a **single** `Sigma.elim` over the whole
/// `isProp` goal (constant motive `λ_. Path (λ_.A) x y`), so no separate `fst`/`snd`
/// (and hence no Σ-iota) is needed. `a` (= A) and `contr` are assumed **closed**
/// (the established helper convention).
///
/// SOUNDNESS: the inner `hcomp`'s cap on each face is `(h x) @ i0 ≡ c` (resp.
/// `(h y) @ i0 ≡ c`), the floor — so it satisfies the enforced `validate_hcomp_cap`
/// (the `i0`-endpoint of `h _ : Path A c _` is `c` by the neutral path-endpoint
/// rule). A genuine proof term: `Sigma.elim` of the `isContr` record plus a
/// type-preserving Kan square.
#[allow(dead_code, non_snake_case)]
pub(crate) fn is_contr_to_is_prop(level: Level, a: &Expr, contr: &Expr) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), x),
            y,
        )
    };
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let path_lam = |body: Expr| {
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(body),
        })
    };
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
            [a.clone(), face, head, tail],
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
        a.clone(),
    );

    // Inner square, built under [x,y,c,h] (then <i>, then each tube's λk).
    //   <i>: [x,y,c,h,i]  ⇒ i=0, h=1, c=2, y=3, x=4.
    //   λk : [x,y,c,h,i,k] ⇒ k=0, i=1, h=2, c=3, y=4, x=5.
    let phi = cofib_or(cofib_eq0(Expr::bvar(0)), cofib_eq1(Expr::bvar(0)));
    let hx = Expr::app(Expr::bvar(2), Expr::bvar(5)); // h x
    let hy = Expr::app(Expr::bvar(2), Expr::bvar(4)); // h y
    let branch_i0 = Expr::lam(BinderInfo::Default, interval(), path_app(hx, Expr::bvar(0)));
    let branch_i1 = Expr::lam(BinderInfo::Default, interval(), path_app(hy, Expr::bvar(0)));
    let system = sys_cons(
        cofib_eq0(Expr::bvar(0)),
        branch_i0,
        sys_cons(cofib_eq1(Expr::bvar(0)), branch_i1, sys_nil),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a.clone()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(Expr::bvar(2)), // c
    });
    let inner = path_lam(hcomp); // <i> hcomp : Path (λ_.A) x y, valid under [x,y,c,h]

    // minor = λ (c:A). λ (h : Π(z:A). Path (λ_.A) c z). inner.
    //   λc: [x,y]; λh: [x,y,c] (c=BVar0); h-domain `Π z. Path A c z` under [x,y,c,z]
    //   has c=BVar1, z=BVar0.
    let h_dom = Expr::pi(
        BinderInfo::Default,
        a.clone(),
        path_homog(&a.lift(1), Expr::bvar(1), Expr::bvar(0)),
    );
    let minor = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(BinderInfo::Default, h_dom, inner),
    );

    // motive M = λ (w:isContr A). Path (λ_.A) x y.  Under [x,y,w]: x=2, y=1.
    let is_contr_a = is_contr_type(level.clone(), a);
    let motive = Expr::lam(
        BinderInfo::Default,
        is_contr_a,
        path_homog(&a.lift(1), Expr::bvar(2), Expr::bvar(1)),
    );

    // body = Sigma.elim.{level} A Bfam M minor contr  (valid under [x,y]).
    let bfam = is_contr_bfam(a);
    let body = Expr::apps(
        Expr::const_(sigma_names::SIGMA_ELIM.clone(), vec![level.clone()]),
        [a.clone(), bfam, motive, minor, contr.clone()],
    );

    // isContr→isProp contr := λ (x:A). λ (y:A). body.
    Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(BinderInfo::Default, a.lift(1), body),
    )
}

/// `isProp→isSet : isProp A → isSet A` — a proposition is a set.
///
/// The standard cubical 2D square (agda/cubical `Foundations/Prelude`):
///
/// ```text
/// isProp→isSet h a b p q := <j> <i> hcomp {A}
///   [ (i=0) ↦ λ k. (h a a) @ k,  (i=1) ↦ λ k. (h a b) @ k,
///     (j=0) ↦ λ k. (h a (p@i)) @ k,  (j=1) ↦ λ k. (h a (q@i)) @ k ] a
/// ```
///
/// At the lid (`k = i1`) the four walls read off `a, b, p i, q i`, so the square
/// has boundary `p ≡ q` (a `Path (Path A a b) p q`), which is `isProp (Path A a b)`
/// for the bound `a b` — i.e. `isSet A`. `a` (= A) and `hprop` are assumed
/// **closed**.
///
/// SOUNDNESS: every wall is `λ k. (h a _) @ k` with `(h a _) : Path A a _`, so its
/// `i0`-cap is `a` = the floor — the four faces are cap-coherent and pass the
/// enforced `validate_hcomp_cap`; the four corner overlaps (e.g. `(i=0)∧(j=0)`)
/// agree on the face because `p i0 ≡ a` (so `h a (p i0) ≡ h a a`), checked by the
/// face-restricted `validate_hcomp_system`. A genuine proof term — no `sorry`.
#[allow(dead_code, non_snake_case)]
pub(crate) fn is_prop_to_is_set(level: Level, a: &Expr, hprop: &Expr) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), x),
            y,
        )
    };
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let path_lam = |body: Expr| {
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(body),
        })
    };
    // System/Cofib heads carry `A`'s carrier universe `level` (`System.cons.{level}
    // {A:Sort level}`); the `A` argument is supplied explicitly into the implicit slot.
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
            [a.clone(), face, head, tail],
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
        a.clone(),
    );

    // Body built under [a,b,p,q] then <j> then <i> then each tube's λk:
    //   <j>: [a,b,p,q,j]       ⇒ j=0,q=1,p=2,b=3,a=4
    //   <i>: [a,b,p,q,j,i]     ⇒ i=0,j=1,q=2,p=3,b=4,a=5
    //   λk : [a,b,p,q,j,i,k]   ⇒ k=0,i=1,j=2,q=3,p=4,b=5,a=6
    let i = || Expr::bvar(1); // i at the λk level
    let hp = |u: Expr, v: Expr| Expr::app(Expr::app(hprop.clone(), u), v); // hprop u v
    let wall = |u: Expr, v: Expr| {
        Expr::lam(
            BinderInfo::Default,
            interval(),
            path_app(hp(u, v), Expr::bvar(0)),
        )
    };
    let a6 = || Expr::bvar(6);
    let b5 = || Expr::bvar(5);
    let p_at_i = path_app(Expr::bvar(4), i()); // p @ i
    let q_at_i = path_app(Expr::bvar(3), i()); // q @ i
    let branch_i0 = wall(a6(), a6()); // h a a
    let branch_i1 = wall(a6(), b5()); // h a b
    let branch_j0 = wall(a6(), p_at_i); // h a (p@i)
    let branch_j1 = wall(a6(), q_at_i); // h a (q@i)

    // φ = (i=0) ∨ (i=1) ∨ (j=0) ∨ (j=1) with i=BVar0, j=BVar1 at the <i> level.
    let phi = cofib_or(
        cofib_or(cofib_eq0(Expr::bvar(0)), cofib_eq1(Expr::bvar(0))),
        cofib_or(cofib_eq0(Expr::bvar(1)), cofib_eq1(Expr::bvar(1))),
    );
    let system = sys_cons(
        cofib_eq0(Expr::bvar(0)),
        branch_i0,
        sys_cons(
            cofib_eq1(Expr::bvar(0)),
            branch_i1,
            sys_cons(
                cofib_eq0(Expr::bvar(1)),
                branch_j0,
                sys_cons(cofib_eq1(Expr::bvar(1)), branch_j1, sys_nil),
            ),
        ),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a.clone()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(Expr::bvar(5)), // a  (floor, at <i> level)
    });
    let square = path_lam(path_lam(hcomp)); // <j> <i> hcomp, valid under [a,b,p,q]

    // λ (a:A) (b:A) (p:Path A a b) (q:Path A a b). square.
    let path_ab = |a_idx, b_idx| path_homog(&a.lift(2), Expr::bvar(a_idx), Expr::bvar(b_idx));
    Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(
            BinderInfo::Default,
            a.lift(1),
            Expr::lam(
                BinderInfo::Default,
                path_ab(1, 0), // p : Path A a b  (a=1,b=0)
                Expr::lam(
                    BinderInfo::Default,
                    path_ab(2, 1), // q : Path A a b  (a=2,b=1)
                    square,
                ),
            ),
        ),
    )
}

/// `toPathP : (coe B i0 i1 b0 ≡ b1) → PathP B b0 b1` — convert a **homogeneous**
/// path in `B i1` (between the transported `b0` and `b1`) into a heterogeneous
/// `PathP` over the line `B : I → Sort`. The cubical `transport`/`PathP`
/// adjunction.
///
/// ```text
/// toPathP q := <i> hcomp { B i } [ (i=1) ↦ λ j. coe (λ k. B k) i1 i (q @ j) ]
///                                 (coe (λ k. B (i ∧ k)) i0 i1 b0)
/// ```
///
/// ## Why the `coe`-corrected single wall (the homogeneous-`hcomp` adaptation)
///
/// The textbook CCHM `toPathP` is a heterogeneous `comp`; Clean's `hcomp` is
/// **homogeneous** with **total** tubes (`System.cons`'s head is typed `I → A` at a
/// fixed `A`). So the wall cannot be the partial `(i=1) ↦ λ_. q@j` (its value
/// `q@j : B i1` is not in `B i` off the face). Instead the wall is `coe`-corrected
/// to land in `B i` everywhere — `coe (λk.B k) i1 i (q@j) : B i` — which **equals
/// `q@j` on the face `i=1`** (degenerate `coe i1 i1`), so the lid still reads `b1`.
/// The floor `coe (λk. B(i∧k)) i0 i1 b0 : B i` reads `b0` at `i=i0` (its line is
/// constant there) and matches the wall's `i0`-cap on the face `i=1` (both reduce
/// to `coe B i0 i1 b0`), so the enforced `validate_hcomp_cap` accepts. A single
/// `(i=1)` wall suffices: at `i=i0` the extent is `⊥`, so the lid is the floor `b0`.
///
/// `b_line` (= B), `b0`, `b1`, `q` are assumed **closed**; `level` is `B`'s value
/// universe. SOUNDNESS: a genuine type-preserving Kan composite — endpoints
/// `b0`/`b1` compute, the cap is coherent, no `sorry`.
#[allow(dead_code, non_snake_case)]
pub(crate) fn to_path_p(level: Level, b_line: &Expr, b0: &Expr, _b1: &Expr, q: &Expr) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let i1 = || Expr::from_kind(ExprKind::CubicalI1);
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let i_min =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MIN.clone(), vec![]), [x, y]);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let coe = |ty: Expr, r: Expr, s: Expr, base: Expr| {
        Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(ty),
            r: Arc::new(r),
            s: Arc::new(s),
            base: Arc::new(base),
        })
    };
    // `B applied at `arg`, with the *line* `b_line` lifted by `d` (the binder depth
    // below the input context at the use site). Lift-correct so `to_path_p` composes
    // inside deeper contexts (the fiber contraction), not only for closed inputs.
    let app_b = |d: u32, arg: Expr| Expr::app(b_line.lift(d), arg);

    // The whole term sits under the outer `<i>` (i = BVar 0 at depth 1).
    let ty_i = app_b(1, Expr::bvar(0)); // B i   (depth 1)

    // floor = coe (λ k. B (i ∧ k)) i0 i1 b0.   Inside <i>,λk (depth 2): i=BVar1, k=BVar0.
    let floor_line = Expr::lam(
        BinderInfo::Default,
        interval(),
        app_b(2, i_min(Expr::bvar(1), Expr::bvar(0))),
    );
    let floor = coe(floor_line, i0(), i1(), b0.lift(1)); // b0 at depth 1

    // tube1 = λ j. coe (λ k. B k) i1 i (q @ j).  Inside <i>,λj,λk (depth 3): k=BVar0;
    // the coe's r/s/base stay at the <i>,λj level (depth 2): i=BVar1, j=BVar0.
    let tube1_line = Expr::lam(BinderInfo::Default, interval(), app_b(3, Expr::bvar(0)));
    let tube1 = Expr::lam(
        BinderInfo::Default,
        interval(),
        coe(
            tube1_line,
            i1(),
            Expr::bvar(1),                      // i
            path_app(q.lift(2), Expr::bvar(0)), // q @ j   (q at depth 2)
        ),
    );

    let phi = cofib_eq1(Expr::bvar(0));
    let system = Expr::apps(
        Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
        [
            ty_i.clone(),
            cofib_eq1(Expr::bvar(0)),
            tube1,
            Expr::app(
                Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level]),
                ty_i.clone(),
            ),
        ],
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(ty_i),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(floor),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// `isProp→PathP : ((i:I) → isProp (B i)) → (b0:B i0) → (b1:B i1) → PathP B b0 b1`
/// — a line of propositions has a (unique) `PathP` between any endpoints.
///
/// Standard recipe: `toPathP (hB i1 (coe B i0 i1 b0) b1)` — `hB i1` proves the
/// transported `coe B i0 i1 b0` equal to `b1` in the prop `B i1`, then [`to_path_p`]
/// lifts that homogeneous path to the heterogeneous `PathP`. `b_line`, `hB`, `b0`,
/// `b1` are assumed **closed**.
///
/// SOUNDNESS: a genuine composite of [`to_path_p`] (a type-preserving Kan square)
/// and the supplied propositionality witness — no `sorry`.
#[allow(dead_code, non_snake_case)]
pub(crate) fn is_prop_to_path_p(
    level: Level,
    b_line: &Expr,
    hB: &Expr,
    b0: &Expr,
    b1: &Expr,
) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let i1 = || Expr::from_kind(ExprKind::CubicalI1);
    // q = hB i1 (coe B i0 i1 b0) b1 : Path (λ_. B i1) (coe B i0 i1 b0) b1.
    let transported = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(b_line.clone()),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(b0.clone()),
    });
    let q = Expr::apps(hB.clone(), [i1(), transported, b1.clone()]);
    to_path_p(level, b_line, b0, b1, &q)
}

/// `biInvToIsEquivOnSet : isSet B → (quasi-inverse data) → isEquiv f` — **for a set
/// `B`, a quasi-inverse makes `f` an equivalence** (its fibers are contractible).
///
/// Inputs (all **closed**): `set_b : isSet B`, and the quasi-inverse record
/// `f : A→B`, `g : B→A`, `eta : (x:A) → g (f x) ≡ x` (`g∘f ~ id_A`),
/// `eps : (y:B) → f (g y) ≡ y` (`f∘g ~ id_B`) — exactly the fields of the kernel's
/// `Equiv.mk`. Result: `isEquiv f = (y:B) → isContr (fiber f y)`.
///
/// ## Construction (the "B is a set" fiber contraction)
///
/// For each `y : B` the fiber `Σ (x:A). Path B (f x) y` is contracted to the centre
/// `(g y, eps y)`. For an arbitrary point `(x, p)` (`p : f x ≡ y`):
/// * the **first** component path `α : g y ≡ x` is the through-the-common-point
///   composite `(cong g p)⁻¹ ∙ eta x`, built as a single cap-coherent `hcomp`
///   `<i> hcomp [ (i=0)↦ cong g p, (i=1)↦ eta x ] (g (f x))`;
/// * the **second** component is a `PathP` over `λ i. Path B (f (α i)) y` between
///   `eps y` and `p`; because `B` is a **set**, each `Path B (f (α i)) y` is a
///   proposition, so [`is_prop_to_path_p`] (`isProp→PathP`) discharges it from
///   `set_b`.
/// The pair is assembled by `ΣPathP` (`<i> Sigma.mk A Bfam (α i) (β i)`), and the
/// whole contraction is discharged by one `Sigma.elim` over the abstract fibre
/// point. `level` is the common universe of `A`/`B`.
///
/// SOUNDNESS: a genuine proof term — no `sorry`, no axiomatized `isEquiv`. The only
/// non-structural input is `set_b` (a *hypothesis*, not an axiom); the contraction's
/// Kan squares (`α`, the `isProp→PathP` composite) are cap-coherent, so the whole
/// term is subject to the enforced `validate_hcomp_cap`.
#[allow(dead_code, non_snake_case, clippy::too_many_arguments)]
pub(crate) fn is_equiv_from_quasi_inv_on_set(
    level: Level,
    a: &Expr,
    b: &Expr,
    set_b: &Expr,
    f: &Expr,
    g: &Expr,
    eta: &Expr,
    eps: &Expr,
) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), x),
            y,
        )
    };
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let path_lam = |body: Expr| {
        Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(body),
        })
    };
    let app = Expr::app;

    // ── fibre data at L1 = [y]  (y = BVar 0) ───────────────────────────────────
    // Bfam = λ (x':A). Path (λ_.B) (f x') y.   under λx': x'=0, y=1.
    let bfam = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        path_homog(b, app(f.clone(), Expr::bvar(0)), Expr::bvar(1)),
    );
    let fiber = sigma_type(level.clone(), a, &bfam); // Σ (x:A). Path B (f x) y
                                                     // centre = Sigma.mk A Bfam (g y) (eps y).
    let center = sigma_mk(
        level.clone(),
        a,
        &bfam,
        app(g.clone(), Expr::bvar(0)),
        app(eps.clone(), Expr::bvar(0)),
    );

    // ── α : g y ≡ x, built at [y,x,p]  (p=0, x=1, y=2) ─────────────────────────
    // r = cong g p = <j> g (p@j) : Path A (g(f x)) (g y).   under <j>: j=0,p=1.
    let cong_g_p = path_lam(app(g.clone(), path_app(Expr::bvar(1), Expr::bvar(0))));
    // s = eta x : Path A (g(f x)) x.   c = g (f x).
    let eta_x = app(eta.clone(), Expr::bvar(1));
    // α = <i'> hcomp {A} [ (i'=0) ↦ λj. r@j,  (i'=1) ↦ λj. s@j ] (g (f x)).
    //   under <i'>: i'=0,p=1,x=2,y=3.  then λj: j=0,i'=1,p=2,x=3,y=4.
    let alpha = {
        let floor = app(g.clone(), app(f.clone(), Expr::bvar(2))); // g (f x), x at <i'> level
        let wall0 = Expr::lam(
            BinderInfo::Default,
            interval(),
            path_app(cong_g_p.lift(2), Expr::bvar(0)),
        );
        let wall1 = Expr::lam(
            BinderInfo::Default,
            interval(),
            path_app(eta_x.lift(2), Expr::bvar(0)),
        );
        let phi = cofib_or(cofib_eq0(Expr::bvar(0)), cofib_eq1(Expr::bvar(0)));
        let sys_cons = |face: Expr, head: Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
                [a.clone(), face, head, tail],
            )
        };
        let sys_nil = Expr::app(
            Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
            a.clone(),
        );
        let system = sys_cons(
            cofib_eq0(Expr::bvar(0)),
            wall0,
            sys_cons(cofib_eq1(Expr::bvar(0)), wall1, sys_nil),
        );
        path_lam(Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(a.clone()),
            phi: Arc::new(phi),
            u: Arc::new(system),
            base: Arc::new(floor),
        }))
    }; // α : Path (λ_.A) (g y) x, at [y,x,p].

    // ── β : PathP (λi. Path B (f (α i)) y) (eps y) p, at [y,x,p] ────────────────
    // Pline = λ i. Path (λ_.B) (f (α@i)) y.   under λi: i=0,p=1,x=2,y=3.
    let alpha_at_i = || path_app(alpha.lift(1), Expr::bvar(0));
    let pline = Expr::lam(
        BinderInfo::Default,
        interval(),
        path_homog(b, app(f.clone(), alpha_at_i()), Expr::bvar(3)),
    );
    // hB = λ i. set_b (f (α@i)) y : (i:I) → isProp (Pline i).
    //
    // `set_b` is the lemma's only input that may be **non-closed** (e.g. a
    // hypothesis bound by an enclosing `λ (s : isSet B)`, as in `windingIsEquiv`).
    // It is the unique use site, under `λy, λx, λp, λi` (= 4 binders) at build time;
    // the later `minor.lift(1)` (for `λw`) and `to_path_p`'s internal `q.lift(2)`
    // (its `<i>, λj`) lift the embedded copy the remaining amount, so a single
    // `lift(4)` here makes the whole lemma lift-correct in `set_b`. (`a`/`b`/`f`/`g`/
    // `eta`/`eps` remain assumed closed — they are concrete consts at every caller.)
    let hb = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::apps(set_b.lift(4), [app(f.clone(), alpha_at_i()), Expr::bvar(3)]),
    );
    let eps_y = app(eps.clone(), Expr::bvar(2)); // at [y,x,p]
    let beta = is_prop_to_path_p(level.clone(), &pline, &hb, &eps_y, &Expr::bvar(0));

    // ── ΣPathP : Path (λ_.fiber) centre (x,p), at [y,x,p] ───────────────────────
    // <i> Sigma.mk A Bfam (α@i) (β@i).   under <i>: i=0,p=1,x=2,y=3.
    let sigma_pathp = {
        let bfam_i = bfam.lift(3); // Bfam references y (BVar0) → BVar3
        let a_i = path_app(alpha.lift(1), Expr::bvar(0));
        let b_i = path_app(beta.lift(1), Expr::bvar(0));
        path_lam(sigma_mk(level.clone(), a, &bfam_i, a_i, b_i))
    };

    // ── minor = λ (x:A). λ (p : Path B (f x) y). ΣPathP, built at L1 ────────────
    let minor = {
        let p_dom = path_homog(b, app(f.clone(), Expr::bvar(0)), Expr::bvar(1)); // at [y,x]
        Expr::lam(
            BinderInfo::Default,
            a.clone(),
            Expr::lam(BinderInfo::Default, p_dom, sigma_pathp),
        )
    };

    // ── contraction = λ (w:fiber). Sigma.elim A Bfam M minor w, at L1 ───────────
    let contraction = {
        // M = λ (w':fiber). Path (λ_.fiber) centre w'.   at [y,w,w']: w'=0,w=1,y=2.
        let motive = Expr::lam(
            BinderInfo::Default,
            fiber.lift(1), // domain fiber at [y,w]
            path_homog(&fiber.lift(2), center.lift(2), Expr::bvar(0)),
        );
        let elim = Expr::apps(
            Expr::const_(sigma_names::SIGMA_ELIM.clone(), vec![level.clone()]),
            [
                a.clone(),
                bfam.lift(1), // Bfam at [y,w]
                motive,
                minor.lift(1), // minor at [y,w]
                Expr::bvar(0), // w
            ],
        );
        Expr::lam(BinderInfo::Default, fiber.clone(), elim)
    };

    // ── isContr (fiber) = Sigma.mk fiber BContr centre contraction, at L1 ───────
    let bcontr = is_contr_bfam(&fiber);
    let is_contr_pair = sigma_mk(level.clone(), &fiber, &bcontr, center, contraction);

    // isEquiv f := λ (y:B). isContr (fiber f y).
    Expr::lam(BinderInfo::Default, b.clone(), is_contr_pair)
}

// ── encode-decode `isSet` (Hedberg-free, via a propositional code family) ───────
//
// The generic "fundamental theorem of identity types" route to `isSet`: given a
// reflexive, **propositional** binary code family `code : A → A → Type` that
// **decodes** to identity (`decode : code x y → x ≡ y`), every path space `x ≡ y`
// is a *retract* of the proposition `code x y`, hence itself a proposition — i.e.
// `A` is a set. No Hedberg square, no decidable equality, no groupoid lemmas
// beyond the existing tested `coe`/`J`/`hcomp` primitives. The lemmas below are
// **lift-correct** (unlike the closed-input `path_compose`/`path_sym`/`path_J`),
// because they are applied to the bound `x`/`y`/`u`/`v` of the `isSet` goal.
//
// SOUNDNESS: every builder emits a plain kernel `Expr` over the existing reduction
// primitives; the only trusted-surface additions remain the Σ axioms. The hcomp
// squares (`sym`/`compose`) reuse the *exact* shapes of the tested closed-input
// `path_sym`/`path_compose`, so they are cap-coherent under the enforced
// `validate_hcomp_cap`; `encode`/`decodeEncode` are a `coe`/`J` whose typing
// is carried by the existing constant-line-`coe` and `J`-β rules.

/// `ap f p := <i> f (p @ i)` — **lift-correct** action-on-paths (`cong`). For
/// `p : Path X l r` and `f : X → Y`, gives `Path Y (f l) (f r)`. `f`, `p` valid in
/// the current context (lifted by one under the introduced `<i>`).
#[allow(dead_code)]
pub(crate) fn ap_cong(f: &Expr, p: &Expr) -> Expr {
    let body = Expr::app(
        f.lift(1),
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(p.lift(1)),
            arg: Arc::new(Expr::bvar(0)),
        }),
    );
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(body),
    })
}

/// **Lift-correct** path inverse `sym p := <i> hcomp {A} [(i=0)↦λj.p@j,
/// (i=1)↦λj.p@i0] (p@i0)` (the same square as the closed-input [`path_sym`], but
/// every captured term is `lift`ed by the binder depth, so `a_ty`/`p` may contain
/// loose `BVar`s — the case at the `isProp`-retract call site). `a_ty` (= `A`) is
/// the type the paths live in; `level` its universe.
#[allow(dead_code)]
fn path_sym_lc(a_ty: &Expr, level: Level, p: &Expr) -> Expr {
    let i0 = || Expr::from_kind(ExprKind::CubicalI0);
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), x),
            y,
        )
    };
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let a1 = a_ty.lift(1); // A under the outer `<i>`
    let endpoint = path_app(p.lift(1), i0()); // p@i0 at depth 1
    let phi = cofib_or(cofib_eq0(Expr::bvar(0)), cofib_eq1(Expr::bvar(0)));
    let branch0 = Expr::lam(
        BinderInfo::Default,
        interval(),
        path_app(p.lift(2), Expr::bvar(0)),
    );
    let branch1 = Expr::lam(BinderInfo::Default, interval(), path_app(p.lift(2), i0()));
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
            [a1.clone(), face, head, tail],
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
        a1.clone(),
    );
    let system = sys_cons(
        cofib_eq0(Expr::bvar(0)),
        branch0,
        sys_cons(cofib_eq1(Expr::bvar(0)), branch1, sys_nil),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a1),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(endpoint),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// **Lift-correct** path composition `p ∙ q := <i> hcomp {A} [(i=0)↦λj.p@i,
/// (i=1)↦λj.q@j] (p@i)` (the same square as the closed-input [`path_compose`], with
/// every captured term `lift`ed). For `p : Path A a b`, `q : Path A b c`, gives
/// `Path A a c`.
#[allow(dead_code)]
fn path_compose_lc(a_ty: &Expr, level: Level, p: &Expr, q: &Expr) -> Expr {
    let interval = || Expr::from_kind(ExprKind::CubicalInterval);
    let cofib_eq0 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ0.clone(), vec![]), arg);
    let cofib_eq1 = |arg: Expr| Expr::app(Expr::const_(kan_names::COFIB_EQ1.clone(), vec![]), arg);
    let cofib_or = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(kan_names::COFIB_OR.clone(), vec![]), x),
            y,
        )
    };
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let a1 = a_ty.lift(1);
    let base = path_app(p.lift(1), Expr::bvar(0)); // p@i at depth 1
    let branch0 = Expr::lam(
        BinderInfo::Default,
        interval(),
        path_app(p.lift(2), Expr::bvar(1)),
    );
    let branch1 = Expr::lam(
        BinderInfo::Default,
        interval(),
        path_app(q.lift(2), Expr::bvar(0)),
    );
    let phi = cofib_or(cofib_eq0(Expr::bvar(0)), cofib_eq1(Expr::bvar(0)));
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
            [a1.clone(), face, head, tail],
        )
    };
    let sys_nil = Expr::app(
        Expr::const_(kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
        a1.clone(),
    );
    let system = sys_cons(
        cofib_eq0(Expr::bvar(0)),
        branch0,
        sys_cons(cofib_eq1(Expr::bvar(0)), branch1, sys_nil),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a1),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(base),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// **Lift-correct** path induction `J P d p := coe^{i0→i1} (λi. P (p@i)
/// (<j>p@(i∧j))) d` (the same line as the closed-input [`path_J`], with `motive_p`
/// and `p` `lift`ed by the line/`<j>` binders). `motive_p : (y:A) → Path A a y →
/// Sort`, `d : P a (refl a)`, `p : Path A a y`; result `P y p`.
#[allow(dead_code, non_snake_case)]
fn path_j_lc(motive_p: &Expr, d: &Expr, p: &Expr) -> Expr {
    let path_app = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    let i_min =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(conn_names::I_MIN.clone(), vec![]), [x, y]);
    // diag = <j> p@(i∧j); under <j>: i=BVar1, j=BVar0; p lifted by 2.
    let diag = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(path_app(p.lift(2), i_min(Expr::bvar(1), Expr::bvar(0)))),
    });
    // BODY = P (p@i) diag; under λi: i=BVar0; motive_p & p lifted by 1.
    let body = Expr::apps(motive_p.lift(1), [path_app(p.lift(1), Expr::bvar(0)), diag]);
    let line = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        body,
    );
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
        s: Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
        base: Arc::new(d.clone()),
    })
}

/// `isPropRetract` — **a retract of a proposition is a proposition**. Given a
/// section/retraction `f : P → Q`, `g : Q → P` with `sect : (u:P) → g (f u) ≡ u`
/// and `qprop : isProp Q`, builds `isProp P = (u v:P) → Path P u v` as
///
/// ```text
/// λ u v. (sym (sect u)) ∙ (ap g (qprop (f u) (f v))) ∙ (sect v)
/// ```
///
/// (`u ⇝ g(f u) ⇝ g(f v) ⇝ v`, the middle leg by `Q` being a prop). `p_ty` (= P)
/// and `f`/`g`/`sect`/`qprop` are valid in the current context (the builders are
/// lift-correct); `level` is `P`'s universe.
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn is_prop_retract(
    p_ty: &Expr,
    level: Level,
    f: &Expr,
    g: &Expr,
    sect: &Expr,
    qprop: &Expr,
) -> Expr {
    // Under [u,v]: u=BVar1, v=BVar0; every captured term lifts by two.
    let p2 = p_ty.lift(2);
    let f2 = f.lift(2);
    let g2 = g.lift(2);
    let sect2 = sect.lift(2);
    let qp2 = qprop.lift(2);

    let fu = Expr::app(f2.clone(), Expr::bvar(1));
    let fv = Expr::app(f2, Expr::bvar(0));
    let qpath = Expr::apps(qp2, [fu, fv]); // Path Q (f u) (f v)
    let cg = ap_cong(&g2, &qpath); // Path P (g(f u)) (g(f v))

    let sect_u = Expr::app(sect2.clone(), Expr::bvar(1)); // Path P (g(f u)) u
    let su = path_sym_lc(&p2, level.clone(), &sect_u); // Path P u (g(f u))
    let sect_v = Expr::app(sect2, Expr::bvar(0)); // Path P (g(f v)) v

    let left = path_compose_lc(&p2, level.clone(), &su, &cg); // Path P u (g(f v))
    let full = path_compose_lc(&p2, level, &left, &sect_v); // Path P u v

    Expr::lam(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::lam(BinderInfo::Default, p_ty.lift(1), full),
    )
}

/// `encode A code r x p := coe (λ i. code x (p@i)) i0 i1 (r x)` — transport the
/// reflexivity witness `r x : code x x` along `p : x ≡ y` to `code x y`. `x`/`p`
/// valid in the current context; `code`/`r` assumed closed.
#[allow(dead_code)]
fn encode_term(code: &Expr, r: &Expr, x: &Expr, p: &Expr) -> Expr {
    // line = λ i. code x (p@i); under λi: x lifted by 1, p lifted by 1.
    let line = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        Expr::apps(
            code.clone(),
            [
                x.lift(1),
                Expr::from_kind(ExprKind::CubicalPathApp {
                    path: Arc::new(p.lift(1)),
                    arg: Arc::new(Expr::bvar(0)),
                }),
            ],
        ),
    );
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
        s: Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
        base: Arc::new(Expr::app(r.clone(), x.clone())),
    })
}

/// `isSetFromEncodeDecode` — **a type with a reflexive, propositional, decoding
/// code family is a set** (the Hedberg-free "fundamental theorem of identity types"
/// criterion). All inputs **closed**; `level` is `A`'s universe (`Sort level`):
///
/// * `a` = `A`,
/// * `code : A → A → Type`,
/// * `r : (x:A) → code x x` (reflexivity),
/// * `decode : (x y:A) → code x y → Path A x y`,
/// * `code_prop : (x y:A) → isProp (code x y)`,
/// * `dr : (x:A) → Path (decode x x (r x)) (refl x)` (the **diagonal** coherence —
///   `decode` sends the reflexive code to `refl`).
///
/// Result `isSet A = (x y:A) → isProp (Path A x y)`: for each `x y`, the path
/// space retracts onto the proposition `code x y` via
/// `encode := λ p. coe (λi. code x (p@i)) i0 i1 (r x)` (section) and `decode x y`
/// (retraction), with `decode∘encode ~ id` proved by `J` from `dr`. [`is_prop_retract`]
/// then makes `Path A x y` a proposition.
///
/// SOUNDNESS: `encode` is a `coe` (type-preserving); `decodeEncode` is a `J` whose
/// base type-checks because `encode x x refl ≡ r x` by the constant-line `coe`
/// rule (`refl @ i ≡ x`); the `isProp`-retract square reuses the tested
/// `path_sym`/`path_compose` shapes. No `sorry`, no axiomatized witness.
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn is_set_from_encode_decode(
    level: Level,
    a: &Expr,
    code: &Expr,
    r: &Expr,
    decode: &Expr,
    code_prop: &Expr,
    dr: &Expr,
) -> Expr {
    // Built under [x,y]: x = BVar1, y = BVar0. `a`/`code`/`r`/`decode`/`code_prop`/
    // `dr` are closed (lifts are no-ops), so we reference them directly.
    let path_xy = path_homog(a, Expr::bvar(1), Expr::bvar(0)); // P = Path A x y

    // f = encode x y = λ (p:P). coe (λi. code x (p@i)) i0 i1 (r x).
    //   under λp → [x,y,p]: x=BVar2, p=BVar0.
    let f = Expr::lam(
        BinderInfo::Default,
        path_xy.clone(),
        encode_term(code, r, &Expr::bvar(2), &Expr::bvar(0)),
    );

    // g = decode x y : Q → P.
    let g = Expr::apps(decode.clone(), [Expr::bvar(1), Expr::bvar(0)]);

    // sect = decodeEncode x y = λ (p:P). J (motive) (dr x) p.
    //   motive_p = λ (y':A)(p':Path A x y'). Path (Path A x y')
    //                (decode x y' (encode x y' p')) p'.
    let sect = {
        // Under λp → [x,y,p]; motive_p built here, J's base `dr x` here.
        // motive_p, under [x,y,p, y', p']: p'=0, y'=1, p=2, y=3, x=4.
        let enc = encode_term(code, r, &Expr::bvar(4), &Expr::bvar(0)); // encode x y' p'
        let decode_app = Expr::apps(decode.clone(), [Expr::bvar(4), Expr::bvar(1), enc]);
        let p_yprime = path_homog(a, Expr::bvar(4), Expr::bvar(1)); // Path A x y'
        let body = path_homog(&p_yprime, decode_app, Expr::bvar(0));
        let motive_p = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            Expr::lam(
                BinderInfo::Default,
                path_homog(a, Expr::bvar(3), Expr::bvar(0)), // Path A x y' at [x,y,p,y']
                body,
            ),
        );
        let base = Expr::app(dr.clone(), Expr::bvar(2)); // dr x at [x,y,p]
        let j = path_j_lc(&motive_p, &base, &Expr::bvar(0)); // p = BVar0
        Expr::lam(BinderInfo::Default, path_xy.clone(), j)
    };

    // qprop = code_prop x y : isProp (code x y).
    let qprop = Expr::apps(code_prop.clone(), [Expr::bvar(1), Expr::bvar(0)]);

    let isprop = is_prop_retract(&path_xy, level, &f, &g, &sect, &qprop);

    Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(BinderInfo::Default, a.lift(1), isprop),
    )
}
