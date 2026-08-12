// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The stuck-recursor case, first slice: **under-applied** recursor spines.
//!
//! ```text
//! under_applied_preserved_cd   : one parallel step keeps the head and the spine length
//! under_applied_star_preserved : …and so does any number of them
//! iota_immune_of_under_applied : hence such a spine is PERMANENTLY iota-dead
//! ```
//!
//! # What this closes
//!
//! `nf_head`'s `neutral` arm needs `iota_immune`, and until now the only supply
//! was `iota_immune_of_dead_const_head` (`iota_immunity.rs`), which requires the
//! head to carry **no recursor metadata**. That leaves exactly one gap: a spine
//! headed by a genuine recursor. This slice closes the half of that gap where the
//! spine is **under-applied** — it has no argument in the major-premise slot at
//! all — which is both common in practice (partial applications like
//! `Nat.rec P z s`) and the case with a purely arithmetic reason to be stuck.
//!
//! The remaining half — a *fully* applied recursor whose major premise is stuck —
//! needs the confluence argument, and is not attempted here.
//!
//! **Update: that confluence argument is now COMPLETE.** The stuck-major
//! classification closes all four alternatives — rigid, lam and δ-dead
//! recmeta-free const in `stuck_major_confluence.rs`, and the const head
//! *carrying* recmeta (the case recorded there as circular) in
//! `stuck_major_recmeta.rs`. So a stuck major provably has no
//! constructor-headed reduct.
//!
//! What is still missing is the **bridge** from that fact to `iota_immune`,
//! i.e. the fully-applied analogue of `iota_immune_of_under_applied`:
//!
//! ```text
//! iota_immune_of_stuck_major
//!   (hdef  : defval_for nm = none)         -- head is δ-dead
//!   (hrec  : recmeta_for nm = some meta)   -- and a genuine recursor
//!   (hhead : kexpr_const_name (kapp_fn r) = some nm)
//!   (hslot : list_head (list_drop (major_idx meta) (kapp_args r)) = some maj)
//!   (hno   : forall cname rule m2, maj =>* m2
//!              -> kexpr_const_name (kapp_fn m2) = some cname
//!              -> recrule_for (red_rec the_red_env) nm cname = some rule -> Empty)
//!   : iota_immune r
//! ```
//!
//! `hno` is exactly what the completed classification supplies, and the ι side
//! of this bridge needs nothing new: `iota_reduct_some_inv_type` — the
//! extraction primitive `iota_step_major_head_none_absurd` and its three
//! siblings are all built on — already yields the firing `cname` and `rule`
//! that `hno` consumes. What is missing is only the spine-preservation half,
//! `major_slot_star_reduces`. Note the
//! warning above still applies to this slice and is the reason `hno` quantifies
//! over reducts of the **major** rather than of its whnf: `wmajor` is *not* a
//! subterm of `e`, because whnf can grow a term through δ-unfolding, so a
//! subterm induction is refutable here.
//!
//! # The shape, which took two wrong guesses to find
//!
//! `iota_step_below_boundary_absurd` (`complete_development.rs`) says a
//! const-headed spine with `Le (length (kapp_args e)) (major_idx meta)` cannot
//! fire ι — the major slot is past the end of the argument list, so
//! `iota_reduct`'s third `opt_bind` yields `none`. To lift that to *permanent*
//! ι-deadness the guard has to survive reduction, and the naive statement does
//! not compose:
//!
//! * Carrying `Le (length q) MI` **upward** fails. The `app` arm would need
//!   `Le (succ (length af2)) MI` from `Le (length af2) MI`, which is backwards.
//! * Carrying it **downward** into the induction hypothesis works, because
//!   `Le (succ n) m -> Le n m` is just `le_trans` with `Le.step n n (Le.refl n)`.
//!
//! So the motive splits the two directions: the `Le` is an **antecedent**, consumed
//! downward and used only by the ι arm, while what travels **upward** is a length
//! *equation* `length (kapp_args q) = length (kapp_args p)`, which composes through
//! `app` by `succ`-congruence. The caller transports the `Le` across that equation
//! at the end.
//!
//! Getting this wrong is not hypothetical: the first sketch for this case proposed
//! a subterm induction, and it is refutable — `wmajor` is **not** a subterm of `e`,
//! because whnf can *grow* a term through δ-unfolding.
//!
//! # How each of the eleven arms closes
//!
//! | arm | resolution |
//! |---|---|
//! | `refl` | hand back the hypothesis with `Eq.refl` |
//! | `app` | `kapp_fn (app f a)` unfolds to `kapp_fn f`, so the head hypothesis passes straight to the IH; the length equation rebuilds by `succ`-congruence |
//! | `beta` | the head would be a `lam`, which has no const name |
//! | `lam`, `pi`, `forall_`, `let_`, `let_cong`, `proj` | the source is its own `kapp_fn`, and none carries a const name |
//! | `iota` | `iota_step_below_boundary_absurd` — **this is where the `Le` is spent** |
//! | `delta` | `delta_reduct_eq_none_of_defval_none` |
//!
//! `DerivedProved` throughout, empty axiom closures.

use super::iota_immunity::ARM_ORDER;
use super::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The major-premise index, as `iota_step_below_boundary_absurd` spells it.
const MI: &str = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) \
     (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";

impl Specification {
    /// Under-applied recursor spines are permanently ι-dead.
    pub(super) fn add_stuck_recursor(&mut self) -> Result<(), SpecError> {
        // ORDER IS LOAD-BEARING. Registration is sequential and each declaration
        // must already see everything it names, so the two shared primitives come
        // first, then the UNDER-APPLIED half — whose preservation lemma the
        // bvar-major half calls in its app arm — and only then the bvar half.
        // Getting this backwards costs a full validation cycle and reports as
        // `Unknown identifier`, not as a dependency error. It cost one here.
        self.add_le_succ_weaken()?;
        self.add_major_head_none_absurd()?;
        self.add_under_applied_preserved()?;
        self.add_under_applied_star()?;
        self.add_iota_immune_under_applied()?;
        self.add_bvar_major_chain()?;
        Ok(())
    }

    /// `kexpr_const_name (kapp_fn {e}) = some nm`.
    fn ua_head_is(e: &str) -> String {
        format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {e})) (OptionType.some Name nm)")
    }

    /// `list_length (kapp_args {e})`.
    fn ua_len_of(e: &str) -> String {
        format!("(list_length (kapp_args {e}))")
    }

    /// The CONTINUATION type: what an arm is handed and must call.
    ///
    /// Distinct from `concl` on purpose. An arm's return type is
    /// `(kont) -> C`, so the arm binds `k` at `kont` — the continuation itself —
    /// and applies it to two arguments. Binding `k` at `concl` instead and then
    /// applying it to two arguments typechecks in Rust and is rejected by the
    /// kernel as `App` vs `Pi`, which is exactly what happened on the first run.
    fn kont(from: &str, to: &str) -> String {
        format!(
            "{} -> Eq Nat {} {} -> C",
            Self::ua_head_is(to),
            Self::ua_len_of(to),
            Self::ua_len_of(from),
        )
    }

    /// The CPS conclusion: the head survives and the length is unchanged.
    fn concl(from: &str, to: &str) -> String {
        format!("({}) -> C", Self::kont(from, to))
    }

    /// The motive's antecedent pair plus its CPS conclusion.
    fn step_goal(from: &str, to: &str) -> String {
        format!(
            "{} -> Le {} {MI} -> {}",
            Self::ua_head_is(from),
            Self::ua_len_of(from),
            Self::concl(from, to),
        )
    }

    /// `length (kapp_args (app f a)) = succ (length (kapp_args f))`.
    ///
    /// `kapp_args (app f a)` unfolds to `list_append (kapp_args f) [a]`, so the
    /// in-tree singleton-append length lemma applies directly.
    fn len_app(f: &str, a: &str) -> String {
        format!("(list_length_append_singleton (kapp_args {f}) {a})")
    }

    /// The major-premise index for an arbitrary metadata binder.
    fn mi_at(m: &str) -> String {
        format!(
            "(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) \
             (recmeta_num_minors {m})) (recmeta_num_indices {m}))"
        )
    }

    /// The prefix count (params + motives + minors) for a metadata binder.
    fn prefix_at(m: &str) -> String {
        format!(
            "(Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) \
             (recmeta_num_minors {m}))"
        )
    }

    /// A STUCK MAJOR PREMISE BLOCKS iota — the primitive the confluence half needs.
    ///
    /// `iota_step_below_boundary_absurd` blocks ι when the major slot does not
    /// exist. This blocks it when the slot exists but what sits there has no
    /// constant at its head, which is the situation for every *stuck* major: a
    /// bound variable, a sort, a lambda, or an application on any of those.
    ///
    /// Both are inversions of the same five-level `opt_bind` chain via
    /// `iota_reduct_some_inv_type`, and this one reuses that proof's
    /// `recname2 = nm` / `meta2 = meta` alignment verbatim. The new step is the
    /// last one: `h3` identifies the recovered major with the caller's, and `h4`
    /// then says it has a const head, contradicting the hypothesis.
    fn add_major_head_none_absurd(&mut self) -> Result<(), SpecError> {
        let mi_meta = Self::mi_at("meta");
        let mi_meta2 = Self::mi_at("meta2");
        let pre2 = Self::prefix_at("meta2");
        // recname2 = nm, from h1 and the caller's head equation.
        let recname2_eq_nm = "(option_some_inj Name recname2 nm \
             (Eq.trans (OptionType Name) (OptionType.some Name recname2) \
             (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) \
             (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname2) h1) hhead))";
        let h2_at_nm = format!(
            "(Eq.substType Name (fun (N : Name) => Eq (OptionType RecMeta) \
             (recmeta_for env N) (OptionType.some RecMeta meta2)) recname2 nm \
             {recname2_eq_nm} h2)"
        );
        let meta2_eq_meta = format!(
            "(option_some_inj RecMeta meta2 meta \
             (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta2) \
             (recmeta_for env nm) (OptionType.some RecMeta meta) \
             (Eq.symm (OptionType RecMeta) (recmeta_for env nm) \
             (OptionType.some RecMeta meta2) {h2_at_nm}) hmeta))"
        );
        // h3 rewritten so its index is the caller's meta, then major = M.
        let h3_at_meta = format!(
            "(Eq.substType RecMeta (fun (M2 : RecMeta) => Eq (OptionType KExpr) \
             (list_head (list_drop {mi} (kapp_args e))) (OptionType.some KExpr major)) \
             meta2 meta {meta2_eq_meta} h3)",
            mi = Self::mi_at("M2"),
        );
        let major_eq_m = format!(
            "(option_some_inj KExpr major mjr \
             (Eq.trans (OptionType KExpr) (OptionType.some KExpr major) \
             (list_head (list_drop {mi_meta} (kapp_args e))) (OptionType.some KExpr mjr) \
             (Eq.symm (OptionType KExpr) (list_head (list_drop {mi_meta} (kapp_args e))) \
             (OptionType.some KExpr major) {h3_at_meta}) hmaj))"
        );
        let h4_at_m = format!(
            "(Eq.substType KExpr (fun (X : KExpr) => Eq (OptionType Name) \
             (kexpr_const_name (kapp_fn X)) (OptionType.some Name cname2)) \
             major mjr {major_eq_m} h4)"
        );
        let reduct2 = format!(
            "(apply_spine (list_drop (Nat.succ {mi_meta2}) (kapp_args e)) \
             (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) \
             (recrule_num_fields rule2)) (kapp_args major)) \
             (apply_spine (list_take {pre2} (kapp_args e)) (recrule_rhs rule2))))"
        );
        self.add_recursive_def(
            &format!(
                "def iota_step_major_head_none_absurd (env : RecEnv) (e : KExpr) (t : KExpr) \
                 (nm : Name) (meta : RecMeta) (mjr : KExpr) (C : Type) \
                 (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
                 (OptionType.some Name nm)) \
                 (hmeta : Eq (OptionType RecMeta) (recmeta_for env nm) \
                 (OptionType.some RecMeta meta)) \
                 (hmaj : Eq (OptionType KExpr) (list_head (list_drop {mi_meta} (kapp_args e))) \
                 (OptionType.some KExpr mjr)) \
                 (hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn mjr)) \
                 (OptionType.none Name)) \
                 (hi : iota_step env e t) : C := \
                 iota_reduct_some_inv_type env e t C hi \
                 (fun (recname2 : Name) (meta2 : RecMeta) (major : KExpr) (cname2 : Name) \
                 (rule2 : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
                 (OptionType.some Name recname2)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname2) \
                 (OptionType.some RecMeta meta2)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {mi_meta2} (kapp_args e))) \
                 (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) \
                 (OptionType.some Name cname2)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname2 cname2) \
                 (OptionType.some RecRule rule2)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct2}) \
                 (OptionType.some KExpr t)) => \
                 option_none_ne_some_type Name cname2 C \
                 (Eq.trans (OptionType Name) (OptionType.none Name) \
                 (kexpr_const_name (kapp_fn mjr)) (OptionType.some Name cname2) \
                 (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn mjr)) \
                 (OptionType.none Name) hnone) {h4_at_m}))"
            ),
            "iota_step_major_head_none_absurd: a recursor spine whose MAJOR PREMISE has no \
             constant at its head cannot fire a top-level iota. \
             \
             This is the primitive the fully-applied stuck-recursor case needs, and the sibling of \
             iota_step_below_boundary_absurd: that one blocks iota when the major slot does not \
             EXIST, this one when the slot exists but holds something stuck — a bound variable, a \
             sort, a lambda, or an application on any of those. Between them they cover both ways \
             a recursor can be stuck. \
             \
             Both invert the same five-level opt_bind chain through iota_reduct_some_inv_type, and \
             this proof reuses that one's recname2 = nm and meta2 = meta alignment verbatim rather \
             than reproving it. The new work is only the last link: rewriting h3's index to the \
             caller's meta identifies the recovered major with the caller's, and h4 — which says \
             that major has a const head — then contradicts the hypothesis directly. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The witness type for a minimally fully-applied recursor spine with a bound
    /// variable in the major slot.
    ///
    /// A single-constructor `Type`-valued record, which is how this codebase
    /// packages an existential (the fragment has no `Exists`). Using a witness
    /// rather than a CPS antecedent matters here: the preservation lemma's motive
    /// must be `Type`-valued for `par_reduces_cd.rec`, and a witness type is
    /// already `Type`-valued, so nothing needs lifting and the statement reads as
    /// what it means — *this term is such a spine*.
    // Staged for the wh-lane's in-flight stuck-recursor bricks; the expect
    // fails loud the moment a caller lands (2026-08-06).
    #[expect(dead_code)]
    fn major_is_bvar(f: &str) -> String {
        format!(
            "(Eq.substType Nat (fun (z : Nat) => Eq (OptionType KExpr) \
             (list_head (list_drop z (kapp_args (KExpr.app {f} (KExpr.bvar bi))))) \
             (OptionType.some KExpr (KExpr.bvar bi))) \
             (list_length (kapp_args {f})) {mi} hlen{f} \
             (list_head_drop_len_append (kapp_args {f}) (KExpr.bvar bi)))",
            mi = Self::mi_at("meta"),
        )
    }

    /// `Le (length (kapp_args F)) major_idx`, from the exact length equation.
    // Staged for the wh-lane's in-flight stuck-recursor bricks; the expect
    // fails loud the moment a caller lands (2026-08-06).
    #[expect(dead_code)]
    fn le_from_len(f: &str) -> String {
        format!(
            "(Eq.subst Nat (fun (z : Nat) => Le z {mi}) {mi} (list_length (kapp_args {f})) \
             (Eq.symm Nat (list_length (kapp_args {f})) {mi} hlen{f}) (Le.refl {mi}))",
            mi = Self::mi_at("meta"),
        )
    }

    /// `head {x} = some nm`.
    fn bm_head(x: &str) -> String {
        format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.some Name nm)")
    }

    /// `length (kapp_args {x}) = major_idx meta` — EXACT, not a bound. This is
    /// what puts the bound variable in the last argument slot, so
    /// `list_head_drop_len_append` finds it with no positional search.
    fn bm_len(x: &str) -> String {
        format!(
            "Eq Nat (list_length (kapp_args {x})) {mi}",
            mi = Self::mi_at("meta")
        )
    }

    /// The CPS invariant at a term: *some* `F` makes it `app F (bvar bi)` with the
    /// right head and argument count.
    ///
    /// Stated in CPS rather than as a witness inductive. A witness type would read
    /// better, but eliminating one needs `BvarMajorSpine.rec`, and a
    /// three-parameter indexed recursor has **no precedent in this tree** — the
    /// first attempt failed with "not a function type, but 4 argument(s) remain",
    /// whose arity fingerprint says the generated recursor does not take the
    /// parameters explicitly. CPS uses only `par_reduces_cd.rec`, whose shape is
    /// already validated twice in this module.
    fn bm_inv(x: &str, var: &str) -> String {
        format!(
            "forall ({var} : KExpr), Eq KExpr {x} (KExpr.app {var} (KExpr.bvar bi)) -> \
             {head} -> {len} -> ",
            head = Self::bm_head(var),
            len = Self::bm_len(var),
        )
    }

    /// The motive: consume the invariant at `p`, hand it back at `q`.
    fn bm_goal(p: &str, q: &str) -> String {
        format!(
            "{ante}({conc}C) -> C",
            ante = Self::bm_inv(p, "F"),
            conc = Self::bm_inv(q, "G"),
        )
    }

    /// The eleven arms of the bvar-major preservation recursion.
    fn bvar_major_arms() -> String {
        let mi = Self::mi_at("meta");
        let maj_at = |f: &str, hlen: &str| {
            format!(
                "(Eq.substType Nat (fun (z : Nat) => Eq (OptionType KExpr) \
                 (list_head (list_drop z (kapp_args (KExpr.app {f} (KExpr.bvar bi))))) \
                 (OptionType.some KExpr (KExpr.bvar bi))) \
                 (list_length (kapp_args {f})) {mi} {hlen} \
                 (list_head_drop_len_append (kapp_args {f}) (KExpr.bvar bi)))"
            )
        };
        let onto = |src: &str, ty: &str, val: &str| {
            format!(
                "(Eq.substType KExpr (fun (X : KExpr) => {ty}) \
                 (KExpr.app F (KExpr.bvar bi)) {src} \
                 (Eq.symm KExpr {src} (KExpr.app F (KExpr.bvar bi)) heq) {val})"
            )
        };
        let mut arms = String::new();
        for (slot, entry) in ARM_ORDER.iter().enumerate() {
            let binders = |src: &str| {
                format!(
                    "(F : KExpr) (heq : Eq KExpr {src} (KExpr.app F (KExpr.bvar bi))) \
                     (hhF : {head}) (hlenF : {len}) (k : {conc}C) ",
                    head = Self::bm_head("F"),
                    len = Self::bm_len("F"),
                    conc = Self::bm_inv("QQ", "G"),
                )
            };
            let _ = &binders;
            match (slot, entry) {
                (0, _) => arms.push_str(&format!(
                    "(fun (re : KExpr) (F : KExpr) \
                     (heq : Eq KExpr re (KExpr.app F (KExpr.bvar bi))) (hhF : {head}) \
                     (hlenF : {len}) (k : {conc}C) => k F heq hhF hlenF) ",
                    head = Self::bm_head("F"),
                    len = Self::bm_len("F"),
                    conc = Self::bm_inv("re", "G"),
                )),
                (7, _) => arms.push_str(&format!(
                    "(fun (ie : KExpr) (ie2 : KExpr) \
                     (hstep : iota_step (red_rec env) ie ie2) (F : KExpr) \
                     (heq : Eq KExpr ie (KExpr.app F (KExpr.bvar bi))) (hhF : {head}) \
                     (hlenF : {len}) (_k : {conc}C) => \
                     iota_step_major_head_none_absurd (red_rec env) ie ie2 nm meta \
                     (KExpr.bvar bi) C {hh} hrec {hm} \
                     (Eq.refl (OptionType Name) (OptionType.none Name)) hstep) ",
                    head = Self::bm_head("F"),
                    len = Self::bm_len("F"),
                    conc = Self::bm_inv("ie2", "G"),
                    hh = onto("ie", &Self::bm_head("X"), "hhF"),
                    hm = onto(
                        "ie",
                        &format!(
                            "Eq (OptionType KExpr) (list_head (list_drop {mi} (kapp_args X))) \
                             (OptionType.some KExpr (KExpr.bvar bi))"
                        ),
                        &maj_at("F", "hlenF"),
                    ),
                )),
                (8, _) => arms.push_str(&format!(
                    "(fun (de : KExpr) (de2 : KExpr) \
                     (hstep : delta_step (red_def env) de de2) (F : KExpr) \
                     (heq : Eq KExpr de (KExpr.app F (KExpr.bvar bi))) (hhF : {head}) \
                     (hlenF : {len}) (_k : {conc}C) => \
                     option_none_ne_some_type KExpr de2 C \
                     (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                     (delta_reduct (red_def env) de) (OptionType.some KExpr de2) \
                     (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) de) \
                     (OptionType.none KExpr) \
                     (delta_reduct_eq_none_of_defval_none (red_def env) de nm {hh} hdef)) \
                     hstep)) ",
                    head = Self::bm_head("F"),
                    len = Self::bm_len("F"),
                    conc = Self::bm_inv("de2", "G"),
                    hh = onto("de", &Self::bm_head("X"), "hhF"),
                )),
                (_, Some(idx)) => {
                    let (payload, pairs, src, tgt) = CD_STRUCTURAL_ARMS[*idx];
                    let is_app = *idx == 1;
                    let mut pb = String::new();
                    let mut ib = String::new();
                    for (n, (from, to)) in pairs.iter().enumerate() {
                        let pn = match (is_app, n) {
                            (true, 0) => "hpf",
                            (true, 1) => "hpa",
                            _ => "_",
                        };
                        pb.push_str(&format!("({pn} : par_reduces_cd env {from} {to}) "));
                        ib.push_str(&format!("(_ : {}) ", Self::bm_goal(from, to)));
                    }
                    let body = if is_app {
                        // heq : app af aa = app F (bvar bi). So af = F and aa is the
                        // bound variable; the reduced function keeps head and count
                        // by the OTHER half's lemma, and the reduced argument is
                        // still a bound variable.
                        let af_eq_f = "(app_inj_fst af aa F (KExpr.bvar bi) heq)";
                        let aa_is_bvar = "(app_inj_snd af aa F (KExpr.bvar bi) heq)";
                        format!(
                            "under_applied_preserved_cd env nm meta hdef hrec C af af2 hpf \
                             (Eq.substType KExpr (fun (X : KExpr) => {headX}) F af \
                             (Eq.symm KExpr af F {af_eq_f}) hhF) \
                             (Eq.subst Nat (fun (z : Nat) => Le z {mi}) {mi} \
                             (list_length (kapp_args af)) \
                             (Eq.symm Nat (list_length (kapp_args af)) {mi} \
                             (Eq.substType KExpr (fun (X : KExpr) => {lenX}) F af \
                             (Eq.symm KExpr af F {af_eq_f}) hlenF)) (Le.refl {mi})) \
                             (fun (hh2 : {head_af2}) \
                             (hlen2 : Eq Nat (list_length (kapp_args af2)) \
                             (list_length (kapp_args af))) => \
                             k af2 \
                             (Eq.cong KExpr KExpr (fun (X : KExpr) => KExpr.app af2 X) aa2 \
                             (KExpr.bvar bi) \
                             (par_reduces_cd_bvar_inv_eq env aa aa2 hpa bi {aa_is_bvar})) \
                             hh2 \
                             (Eq.trans Nat (list_length (kapp_args af2)) \
                             (list_length (kapp_args af)) {mi} hlen2 \
                             (Eq.substType KExpr (fun (X : KExpr) => {lenX}) F af \
                             (Eq.symm KExpr af F {af_eq_f}) hlenF)))",
                            headX = Self::bm_head("X"),
                            lenX = Self::bm_len("X"),
                            head_af2 = Self::bm_head("af2"),
                        )
                    } else if *idx == 0 {
                        // BETA IS NOT TAG-DISCRIMINABLE. Its source `app (lam A b) arg`
                        // is itself an application, so it has the SAME kexpr_tag as
                        // `app F (bvar bi)` and the generic discriminator does not
                        // apply — it reports `nat_eqb 2 2`, which is true, not false.
                        // Kill it by the HEAD instead: app_inj_fst identifies F with
                        // the lambda, and a lambda has no constant at its head.
                        //
                        // The under-applied half never hit this because its hypothesis
                        // was about the source directly, where the head is already
                        // `none`; here it is about F, one indirection away.
                        format!(
                            "option_none_ne_some_type Name nm C \
                             (Eq.substType KExpr (fun (X : KExpr) => {headX}) F \
                             (KExpr.lam bA bbody) \
                             (Eq.symm KExpr (KExpr.lam bA bbody) F \
                             (app_inj_fst (KExpr.lam bA bbody) barg F (KExpr.bvar bi) heq)) \
                             hhF)",
                            headX = Self::bm_head("X"),
                        )
                    } else {
                        format!(
                            "kexpr_discr_t C {src} (KExpr.app F (KExpr.bvar bi)) heq \
                             (Eq.refl Bool Bool.false)"
                        )
                    };
                    arms.push_str(&format!(
                        "(fun {payload} {pb}{ib}(F : KExpr) \
                         (heq : Eq KExpr {src} (KExpr.app F (KExpr.bvar bi))) (hhF : {head}) \
                         (hlenF : {len}) (k : {conc}C) => {body}) ",
                        head = Self::bm_head("F"),
                        len = Self::bm_len("F"),
                        conc = Self::bm_inv(tgt, "G"),
                    ));
                }
                _ => unreachable!(),
            }
        }
        arms
    }

    fn add_bvar_major_chain(&mut self) -> Result<(), SpecError> {
        let mi = Self::mi_at("meta");
        let params = "(env : RedEnv) (nm : Name) (meta : RecMeta) (bi : Nat) \
             (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) \
             (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) \
             (OptionType.some RecMeta meta)) (C : Type) ";
        // The major of `app F (bvar bi)` is the bound variable, by computation.
        let maj_at = |f: &str, hlen: &str| {
            format!(
                "(Eq.substType Nat (fun (z : Nat) => Eq (OptionType KExpr) \
                 (list_head (list_drop z (kapp_args (KExpr.app {f} (KExpr.bvar bi))))) \
                 (OptionType.some KExpr (KExpr.bvar bi))) \
                 (list_length (kapp_args {f})) {mi} {hlen} \
                 (list_head_drop_len_append (kapp_args {f}) (KExpr.bvar bi)))"
            )
        };
        // Transport a fact about `app F (bvar bi)` onto the arm's source.
        let _onto = |src: &str, ty: &str, val: &str| {
            format!(
                "(Eq.substType KExpr (fun (X : KExpr) => {ty}) \
                 (KExpr.app F (KExpr.bvar bi)) {src} \
                 (Eq.symm KExpr {src} (KExpr.app F (KExpr.bvar bi)) heq) {val})"
            )
        };

        let arms = Self::bvar_major_arms();

        self.add_recursive_def(
            &format!(
                "def bvar_major_preserved_cd {params}(e : KExpr) (e2 : KExpr) \
                 (h : par_reduces_cd env e e2) : {goal} := \
                 par_reduces_cd.rec env \
                 (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd env p q) => {motive}) \
                 {arms}e e2 h",
                goal = Self::bm_goal("e", "e2"),
                motive = Self::bm_goal("p", "q"),
            ),
            "bvar_major_preserved_cd: the canonical stuck-recursor shape — a recursor spine \
             carrying EXACTLY major_idx arguments applied to a bound variable — survives one \
             parallel step. \
             \
             The invariant is CPS rather than a witness inductive. A witness type reads better, \
             and was tried first; eliminating one needs a THREE-PARAMETER INDEXED RECURSOR, which \
             has no precedent in this tree, and the attempt failed with `not a function type, but \
             4 argument(s) remain` — an arity fingerprint saying the generated recursor does not \
             take the parameters explicitly. CPS needs only par_reduces_cd.rec, already validated \
             twice in this module. Reusing a known-good elimination beat introducing an unknown \
             one. \
             \
             The app arm composes the other half rather than re-deriving it: \
             under_applied_preserved_cd keeps the function's head and argument count (its Le is \
             immediate from the EXACT length equation), and par_reduces_cd_bvar_inv_eq keeps the \
             argument a bound variable. The iota arm is blocked by \
             iota_step_major_head_none_absurd — the exact length equation makes the major the last \
             argument, list_head_drop_len_append identifies it, and a bound variable has no \
             constant at its head. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def bvar_major_star_preserved {params}(e : KExpr) (e2 : KExpr) \
                 (h : par_reduces_cd_star env e e2) : {goal} := \
                 par_reduces_cd_star.rec env \
                 (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd_star env p q) => {motive}) \
                 (fun (re : KExpr) (F : KExpr) \
                 (heq : Eq KExpr re (KExpr.app F (KExpr.bvar bi))) (hhF : {headF}) \
                 (hlenF : {lenF}) (k : {conc_re}C) => k F heq hhF hlenF) \
                 (fun (sx : KExpr) (sy : KExpr) (sz : KExpr) \
                 (hstep : par_reduces_cd env sx sy) \
                 (_hstar : par_reduces_cd_star env sy sz) \
                 (ih : {ih_ty}) (F : KExpr) \
                 (heq : Eq KExpr sx (KExpr.app F (KExpr.bvar bi))) (hhF : {headF}) \
                 (hlenF : {lenF}) (k : {conc_sz}C) => \
                 bvar_major_preserved_cd env nm meta bi hdef hrec C sx sy hstep F heq hhF hlenF \
                 (fun (G : KExpr) (heq1 : Eq KExpr sy (KExpr.app G (KExpr.bvar bi))) \
                 (hh1 : {headG}) (hlen1 : {lenG}) => ih G heq1 hh1 hlen1 k)) \
                 e e2 h",
                goal = Self::bm_goal("e", "e2"),
                motive = Self::bm_goal("p", "q"),
                headF = Self::bm_head("F"),
                lenF = Self::bm_len("F"),
                headG = Self::bm_head("G"),
                lenG = Self::bm_len("G"),
                conc_re = Self::bm_inv("re", "G"),
                conc_sz = Self::bm_inv("sz", "G"),
                ih_ty = Self::bm_goal("sy", "sz"),
            ),
            "bvar_major_star_preserved: the shape survives arbitrarily many parallel steps. The \
             two-arm reflexive-transitive induction — the step arm advances one link and hands the \
             recovered F straight to the induction hypothesis, with the caller's continuation \
             threaded through unchanged. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def iota_immune_of_bvar_major (nm : Name) (meta : RecMeta) (bi : Nat) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) \
                 (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) \
                 (OptionType.some RecMeta meta)) \
                 (F : KExpr) (hhF : {headF}) (hlenF : {lenF}) : \
                 iota_immune (KExpr.app F (KExpr.bvar bi)) := \
                 fun (e2 : KExpr) (r : KExpr) \
                 (hstar : par_reduces_cd_star the_red_env \
                 (KExpr.app F (KExpr.bvar bi)) e2) \
                 (hfire : iota_step (red_rec the_red_env) e2 r) => \
                 bvar_major_star_preserved the_red_env nm meta bi hdef hrec Empty \
                 (KExpr.app F (KExpr.bvar bi)) e2 hstar F \
                 (Eq.refl KExpr (KExpr.app F (KExpr.bvar bi))) hhF hlenF \
                 (fun (G : KExpr) (heq : Eq KExpr e2 (KExpr.app G (KExpr.bvar bi))) \
                 (hhG : {headG}) (hlenG : {lenG}) => \
                 iota_step_major_head_none_absurd (red_rec the_red_env) e2 r nm meta \
                 (KExpr.bvar bi) Empty \
                 (Eq.substType KExpr (fun (X : KExpr) => {headX}) \
                 (KExpr.app G (KExpr.bvar bi)) e2 \
                 (Eq.symm KExpr e2 (KExpr.app G (KExpr.bvar bi)) heq) hhG) hrec \
                 (Eq.substType KExpr (fun (X : KExpr) => Eq (OptionType KExpr) \
                 (list_head (list_drop {mi} (kapp_args X))) \
                 (OptionType.some KExpr (KExpr.bvar bi))) \
                 (KExpr.app G (KExpr.bvar bi)) e2 \
                 (Eq.symm KExpr e2 (KExpr.app G (KExpr.bvar bi)) heq) {majG}) \
                 (Eq.refl (OptionType Name) (OptionType.none Name)) hfire)",
                headF = Self::bm_head("F"),
                lenF = Self::bm_len("F"),
                headG = Self::bm_head("G"),
                lenG = Self::bm_len("G"),
                headX = Self::bm_head("X"),
                majG = maj_at("G", "hlenG"),
            ),
            "iota_immune_of_bvar_major: THE SECOND HALF — a recursor spine carrying exactly \
             major_idx arguments and applied to a bound variable is PERMANENTLY iota-dead. \
             \
             This is the canonical stuck recursor, Nat.rec P z s (bvar i): the shape that arises \
             whenever a recursor is eliminated under a binder, which is most of dependent \
             elimination. Together with iota_immune_of_under_applied it covers both ways such a \
             spine is stuck — the major absent, and the major present but never able to become a \
             constructor. \
             \
             Both halves are the same two moves: carry an invariant through reduction, then \
             convert it into the impossibility of a top iota with the matching absurdity lemma. \
             \
             WHAT REMAINS of the stuck-recursor case: a major stuck for some OTHER reason — a \
             const-headed spine that is itself stuck — and spines with arguments PAST the major \
             slot. Both need positional tracking through kapp_args rather than the last-argument \
             shortcut this uses. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_le_succ_weaken(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def le_succ_weaken (n : Nat) (m : Nat) (h : Le (Nat.succ n) m) : Le n m := \
             le_trans n (Nat.succ n) m (Le.step n n (Le.refl n)) h",
            "le_succ_weaken: Le (succ n) m implies Le n m. Free from le_trans, since Le n (succ n) \
             is Le.step n n (Le.refl n). \
             \
             This is the lemma that makes the under-applied guard compose: the app arm must hand \
             its induction hypothesis a bound on the FUNCTION's argument count, and it holds one \
             on the whole application's, which is one larger. Weakening is available in that \
             direction and only that direction — which is precisely why the length is carried back \
             UP as an equation rather than as another bound. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn under_applied_arms() -> String {
        let mut arms = String::new();
        for (slot, entry) in ARM_ORDER.iter().enumerate() {
            match entry {
                None => arms.push_str(&Self::special_arm_ua(slot)),
                Some(idx) => {
                    let (payload, pairs, src, tgt) = CD_STRUCTURAL_ARMS[*idx];
                    let is_app = *idx == 1;
                    let mut proofs = String::new();
                    let mut ihs = String::new();
                    for (n, (from, to)) in pairs.iter().enumerate() {
                        let pn = if is_app && n == 0 { "_hpf" } else { "_" };
                        let inn = if is_app && n == 0 { "ihf" } else { "_" };
                        proofs.push_str(&format!("({pn} : par_reduces_cd env {from} {to}) "));
                        ihs.push_str(&format!("({inn} : {}) ", Self::step_goal(from, to)));
                    }
                    let body = if is_app {
                        // The head passes to the IH definitionally (kapp_fn of an
                        // application unfolds to kapp_fn of its function). The Le
                        // weakens down; the length equation rebuilds up.
                        format!(
                            "ihf hh \
                             (le_succ_weaken {len_af} {MI} \
                             (Eq.subst Nat (fun (z : Nat) => Le z {MI}) {len_src} \
                             (Nat.succ {len_af}) {lenapp_src} hl)) \
                             (fun (hh2 : {head_af2}) (hlen2 : Eq Nat {len_af2} {len_af}) => \
                             k hh2 \
                             (Eq.trans Nat {len_tgt} (Nat.succ {len_af2}) {len_src} \
                             {lenapp_tgt} \
                             (Eq.trans Nat (Nat.succ {len_af2}) (Nat.succ {len_af}) {len_src} \
                             (Eq.cong Nat Nat Nat.succ {len_af2} {len_af} hlen2) \
                             (Eq.symm Nat {len_src} (Nat.succ {len_af}) {lenapp_src}))))",
                            len_af = Self::ua_len_of("af"),
                            len_af2 = Self::ua_len_of("af2"),
                            len_src = Self::ua_len_of(src),
                            len_tgt = Self::ua_len_of(tgt),
                            head_af2 = Self::ua_head_is("af2"),
                            lenapp_src = Self::len_app("af", "aa"),
                            lenapp_tgt = Self::len_app("af2", "aa2"),
                        )
                    } else {
                        // A binder/let_/proj/lam-headed source has no const name.
                        "option_none_ne_some_type Name nm C hh".to_string()
                    };
                    let (hl_bind, k_bind) = if is_app { ("hl", "k") } else { ("_hl", "_k") };
                    arms.push_str(&format!(
                        "(fun {payload} {proofs}{ihs}(hh : {head_src}) \
                         ({hl_bind} : Le {len_src} {MI}) ({k_bind} : {kont}) => {body}) ",
                        head_src = Self::ua_head_is(src),
                        len_src = Self::ua_len_of(src),
                        kont = Self::kont(src, tgt),
                    ));
                }
            }
        }
        arms
    }

    /// `refl`, `iota` and `delta` — the three arms with no `CD_STRUCTURAL_ARMS` row.
    fn special_arm_ua(slot: usize) -> String {
        match slot {
            0 => format!(
                "(fun (re : KExpr) (hh : {head}) (_hl : Le {len} {MI}) (k : {kont}) => \
                 k hh (Eq.refl Nat {len})) ",
                head = Self::ua_head_is("re"),
                len = Self::ua_len_of("re"),
                kont = Self::kont("re", "re"),
            ),
            7 => format!(
                "(fun (ie : KExpr) (ie2 : KExpr) \
                 (hstep : iota_step (red_rec env) ie ie2) (hh : {head}) \
                 (hl : Le {len} {MI}) (_k : {kont}) => \
                 iota_step_below_boundary_absurd (red_rec env) ie ie2 nm meta C hh hrec hl hstep) ",
                head = Self::ua_head_is("ie"),
                len = Self::ua_len_of("ie"),
                kont = Self::kont("ie", "ie2"),
            ),
            8 => format!(
                "(fun (de : KExpr) (de2 : KExpr) \
                 (hstep : delta_step (red_def env) de de2) (hh : {head}) \
                 (_hl : Le {len} {MI}) (_k : {kont}) => \
                 option_none_ne_some_type KExpr de2 C \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                 (delta_reduct (red_def env) de) (OptionType.some KExpr de2) \
                 (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) de) \
                 (OptionType.none KExpr) \
                 (delta_reduct_eq_none_of_defval_none (red_def env) de nm hh hdef)) \
                 hstep)) ",
                head = Self::ua_head_is("de"),
                len = Self::ua_len_of("de"),
                kont = Self::kont("de", "de2"),
            ),
            other => unreachable!("slot {other} is a structural row"),
        }
    }

    /// The shared parameter block: the environment, the head name and its metadata.
    fn ua_params() -> String {
        "(env : RedEnv) (nm : Name) (meta : RecMeta) \
         (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) \
         (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) \
         (OptionType.some RecMeta meta)) (C : Type) "
            .to_string()
    }

    fn add_under_applied_preserved(&mut self) -> Result<(), SpecError> {
        let arms = Self::under_applied_arms();
        self.add_recursive_def(
            &format!(
                "def under_applied_preserved_cd {params}(e : KExpr) (e2 : KExpr) \
                 (h : par_reduces_cd env e e2) : {goal} := \
                 par_reduces_cd.rec env \
                 (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd env p q) => {motive}) \
                 {arms}e e2 h",
                params = Self::ua_params(),
                goal = Self::step_goal("e", "e2"),
                motive = Self::step_goal("p", "q"),
            ),
            "under_applied_preserved_cd: one parallel step out of an UNDER-APPLIED recursor spine \
             keeps its head constant and its argument count. \
             \
             The motive deliberately splits two directions that do not both compose. The bound \
             Le (length (kapp_args p)) major_idx is an ANTECEDENT, consumed downward — the app arm \
             weakens it by le_succ_weaken before handing it to the induction hypothesis, and the \
             iota arm spends it on iota_step_below_boundary_absurd. What travels back UP is a \
             length EQUATION, which rebuilds through app by succ-congruence. Carrying the bound \
             upward instead would require Le (succ n) m from Le n m, which is backwards and false. \
             \
             C is a parameter rather than an inner quantifier, so the statement stays in Sort 1: \
             `forall (C : Type), … -> C` would be Sort 2 and nothing in the tree discharges a \
             Sort 2 goal from an absurd hypothesis. \
             \
             Seven of the eight structural arms close identically — a binder, let_, proj or \
             lam-headed source is its own kapp_fn and carries no const name — leaving app as the \
             only substantive one, where kapp_fn (app f a) unfolds to kapp_fn f so the head \
             hypothesis passes to the induction hypothesis untouched. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    fn add_under_applied_star(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!(
                "def under_applied_star_preserved {params}(e : KExpr) (e2 : KExpr) \
                 (h : par_reduces_cd_star env e e2) : {goal} := \
                 par_reduces_cd_star.rec env \
                 (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd_star env p q) => {motive}) \
                 (fun (re : KExpr) (hh : {head_re}) (_hl : Le {len_re} {MI}) \
                 (k : {kont_re}) => k hh (Eq.refl Nat {len_re})) \
                 (fun (sx : KExpr) (sy : KExpr) (sz : KExpr) \
                 (hstep : par_reduces_cd env sx sy) \
                 (_hstar : par_reduces_cd_star env sy sz) \
                 (ih : {ih_ty}) (hh : {head_sx}) (hl : Le {len_sx} {MI}) \
                 (k : {kont_sx_sz}) => \
                 under_applied_preserved_cd env nm meta hdef hrec C sx sy hstep hh hl \
                 (fun (hh1 : {head_sy}) (hlen1 : Eq Nat {len_sy} {len_sx}) => \
                 ih hh1 (Eq.subst Nat (fun (z : Nat) => Le z {MI}) {len_sx} {len_sy} \
                 (Eq.symm Nat {len_sy} {len_sx} hlen1) hl) \
                 (fun (hh2 : {head_sz}) (hlen2 : Eq Nat {len_sz} {len_sy}) => \
                 k hh2 (Eq.trans Nat {len_sz} {len_sy} {len_sx} hlen2 hlen1)))) \
                 e e2 h",
                params = Self::ua_params(),
                goal = Self::step_goal("e", "e2"),
                motive = Self::step_goal("p", "q"),
                head_re = Self::ua_head_is("re"),
                len_re = Self::ua_len_of("re"),
                kont_re = Self::kont("re", "re"),
                ih_ty = Self::step_goal("sy", "sz"),
                head_sx = Self::ua_head_is("sx"),
                head_sy = Self::ua_head_is("sy"),
                head_sz = Self::ua_head_is("sz"),
                len_sx = Self::ua_len_of("sx"),
                len_sy = Self::ua_len_of("sy"),
                len_sz = Self::ua_len_of("sz"),
                kont_sx_sz = Self::kont("sx", "sz"),
            ),
            "under_applied_star_preserved: the head and the argument count survive arbitrarily \
             many parallel steps. The two-arm reflexive-transitive induction, with one wrinkle the \
             single-step version does not have: the bound must be RE-ESTABLISHED at the \
             intermediate term before the induction hypothesis will accept it, by transporting it \
             across the length equation the first step just produced. That is exactly why the \
             equation is the thing carried upward. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_iota_immune_under_applied(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!(
                "def iota_immune_of_under_applied (nm : Name) (meta : RecMeta) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) \
                 (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) \
                 (OptionType.some RecMeta meta)) \
                 (e : KExpr) (hh : {head_e}) (hl : Le {len_e} {MI}) : iota_immune e := \
                 fun (e2 : KExpr) (r : KExpr) \
                 (hstar : par_reduces_cd_star the_red_env e e2) \
                 (hfire : iota_step (red_rec the_red_env) e2 r) => \
                 under_applied_star_preserved the_red_env nm meta hdef hrec Empty e e2 hstar hh hl \
                 (fun (hh2 : {head_e2}) (hlen2 : Eq Nat {len_e2} {len_e}) => \
                 iota_step_below_boundary_absurd (red_rec the_red_env) e2 r nm meta Empty hh2 hrec \
                 (Eq.subst Nat (fun (z : Nat) => Le z {MI}) {len_e} {len_e2} \
                 (Eq.symm Nat {len_e2} {len_e} hlen2) hl) hfire)",
                head_e = Self::ua_head_is("e"),
                head_e2 = Self::ua_head_is("e2"),
                len_e = Self::ua_len_of("e"),
                len_e2 = Self::ua_len_of("e2"),
            ),
            "iota_immune_of_under_applied: THE PAYOFF — an under-applied recursor spine is \
             PERMANENTLY iota-dead. \
             \
             This is the second supply for iota_immune at an application, and it reaches where the \
             first could not. iota_immune_of_dead_const_head (iota_immunity.rs) requires the head \
             to carry NO recursor metadata; this one applies precisely when it does, provided the \
             spine has no argument in the major-premise slot. Partial applications of recursors — \
             Nat.rec P z s with the major still to come — are exactly that shape, and they are \
             everywhere in practice. \
             \
             The argument is arithmetic rather than semantic: iota_reduct's third opt_bind reads \
             the major premise out of the argument list by index, and an index past the end yields \
             none. Head preservation and length preservation carry that fact to every reduct, and \
             iota_step_below_boundary_absurd converts it into the impossibility of a top iota. \
             \
             WHAT REMAINS of the stuck-recursor case: a FULLY applied recursor whose major premise \
             is itself stuck. That needs a confluence argument — the reachable majors of a reduct \
             are reducts of the major, not of its whnf — and it is not attempted here. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `Le` bound must be an ANTECEDENT and the length an EQUATION. If the
    /// bound were carried in the conclusion too, the `app` arm would need
    /// `Le (succ n) m` from `Le n m` — backwards, and false. This is the shape
    /// the whole proof turns on.
    #[test]
    fn test_bound_flows_down_and_equation_flows_up() {
        let goal = Specification::step_goal("p", "q");
        assert!(
            goal.contains(&format!("-> Le {} {MI} ->", Specification::ua_len_of("p"))),
            "the bound must be an antecedent, stated at the SOURCE: {goal}"
        );
        let concl = Specification::concl("p", "q");
        assert!(
            !concl.contains("Le "),
            "the conclusion must carry no bound — only the head and the length equation: {concl}"
        );
        assert!(
            concl.contains(&format!(
                "Eq Nat {} {}",
                Specification::ua_len_of("q"),
                Specification::ua_len_of("p")
            )),
            "the length equation must point from target back to source: {concl}"
        );
    }

    /// `k` is bound at the CONTINUATION type, never at the CPS type.
    ///
    /// An arm returns `(kont) -> C`, so it binds `k : kont` and applies it to two
    /// arguments. Binding `k : concl` and applying it to two arguments is
    /// well-formed Rust string-building and a kernel type error — `App` where
    /// `Pi` was expected. That is precisely how the first run of this lemma
    /// failed, at a cost of one 25-minute cycle, and the shapes are similar
    /// enough that reading the term does not reveal it.
    #[test]
    fn test_k_is_bound_at_the_continuation_not_the_cps_type() {
        let kont = Specification::kont("p", "q");
        let concl = Specification::concl("p", "q");
        assert!(
            !kont.starts_with('('),
            "kont is the continuation itself, not a wrapper: {kont}"
        );
        assert_eq!(
            concl,
            format!("({kont}) -> C"),
            "concl must be exactly kont wrapped and answered"
        );
        let arms = Specification::under_applied_arms();
        assert!(
            !arms.contains(&format!("(k : ({kont}) -> C)")),
            "no arm may bind k at the CPS type"
        );
    }

    /// Exactly one arm may spend the bound — the `iota` arm. If another did, the
    /// proof would be relying on the guard somewhere it has not been established.
    #[test]
    fn test_only_the_iota_arm_spends_the_bound() {
        let arms = Specification::under_applied_arms();
        assert_eq!(
            arms.matches("iota_step_below_boundary_absurd").count(),
            1,
            "the boundary absurdity is the ι arm's alone"
        );
        // Every other arm binds the bound as unused (`_hl`) except `app`, which
        // weakens it downward.
        assert_eq!(
            arms.matches("le_succ_weaken").count(),
            1,
            "only the app arm weakens the bound for its induction hypothesis"
        );
    }

    /// The bvar-major half CALLS the under-applied half, so it must be
    /// registered after it. Registration is sequential; a backwards order reports
    /// as `Unknown identifier` at spec-build time, 25 minutes later.
    #[test]
    fn test_bvar_half_is_registered_after_the_under_applied_half() {
        let src = include_str!("stuck_recursor.rs");
        let body = src
            .split("pub(super) fn add_stuck_recursor")
            .nth(1)
            .expect("the registration function");
        let ua = body
            .find("self.add_under_applied_preserved()")
            .expect("under-applied registration");
        let bv = body
            .find("self.add_bvar_major_chain()")
            .expect("bvar registration");
        assert!(
            ua < bv,
            "the bvar half calls under_applied_preserved_cd, so it must register later"
        );
        assert!(
            Specification::bvar_major_arms().contains("under_applied_preserved_cd"),
            "...and it really does call it — if that stops being true, drop this test"
        );
    }

    /// The BETA arm must NOT be tag-discriminated.
    ///
    /// Every other shape-impossible arm has a source whose `kexpr_tag` differs
    /// from an application's, so `kexpr_discr_t` kills it. Beta's source is
    /// `app (lam A b) arg` — itself an application, same tag — so the
    /// discriminator computes `nat_eqb 2 2`, which is `true`, and the arm does not
    /// typecheck. It has to die by the head instead: `app_inj_fst` identifies `F`
    /// with the lambda, and a lambda carries no constant at its head.
    ///
    /// This cost a cycle. The under-applied half never hit it because its
    /// hypothesis is about the source term directly, where the head is already
    /// `none`; here it is about `F`, one indirection away.
    #[test]
    fn test_beta_arm_dies_by_head_not_by_tag() {
        let arms = Specification::bvar_major_arms();
        assert!(
            arms.contains("app_inj_fst (KExpr.lam bA bbody) barg F (KExpr.bvar bi) heq"),
            "the beta arm must identify F with the lambda and refute via its head"
        );
        // Six tag-discriminations: lam, pi, forall_, let_, let_cong, proj — NOT beta.
        assert_eq!(
            arms.matches("kexpr_discr_t C").count(),
            6,
            "only the six arms whose source is not an application may discriminate by tag"
        );
    }

    /// Eleven arms, matching `par_reduces_cd`'s constructor count and order.
    ///
    /// Counts TOP-LEVEL lambdas only. The first version of this test counted
    /// every `(fun ` and got 13, because the `app` arm's body contains two nested
    /// lambdas of its own — the continuation and the `Eq.subst` motive. Counting
    /// at depth is the recurring way these tests measure the wrong thing.
    #[test]
    fn test_eleven_arms_in_constructor_order() {
        assert_eq!(ARM_ORDER.len(), 11);
        let arms = Specification::under_applied_arms();
        let mut depth = 0i64;
        let mut top = 0usize;
        for (idx, ch) in arms.char_indices() {
            match ch {
                '(' => {
                    if depth == 0 && arms[idx..].starts_with("(fun ") {
                        top += 1;
                    }
                    depth += 1;
                }
                ')' => depth -= 1,
                _ => {}
            }
        }
        assert_eq!(top, 11, "one top-level arm per par_reduces_cd constructor");
        assert_eq!(depth, 0, "balanced");
        // Seven of the eight structural arms are shape-impossible and close
        // identically; only `app` is substantive.
        assert_eq!(
            arms.matches("option_none_ne_some_type Name nm C hh")
                .count(),
            7,
            "beta, lam, pi, forall_, let_, let_cong and proj all die the same way"
        );
    }
}
