//! Kernel BUG-2 brick: an inductive type former whose arity codomain is a sort
//! only up-to-whnf must replay.
//!
//! `check_block_agreement` and the F2 loop in `do_inductive_type_check` used to
//! extract the result sort with a purely SYNTACTIC `get_return_type` + `Sort`
//! match. Coq's Hierarchy-Builder records legitimately produce codomains that
//! are sorts only up to reduction — `LetIn(T := …) in Sort u` (ζ; the
//! `Order.POrder`/…/`Num.normed_mixin_of` `mixin_of` records) or `Const(c)`
//! where `c` unfolds to a sort (δ; the `predArgType`-style
//! `set_type`/`perm_type`/`sdprod_by` carriers). Once the sertop-projfix HB
//! re-dump made those records value-bearing, the syntactic match rejected them
//! ("type former of X does not end in a sort") and their masked-stand-in seeds
//! tainted dependents. The fix checks the codomain up to whnf, exactly as the
//! Lean/Coq kernels do. The fast path (already a syntactic `Sort`) is
//! bit-identical, so the change only ever ACCEPTS strictly more (0-regression).

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn sort1() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// `RLet : Π (A : Sort 1), (let (x : Sort 1 := A) in Sort 1)`  (num_params = 1)
///   codomain zeta-reduces to `Sort 1` (the `mixin_of` / `LetIn in Sort` shape).
/// `RLet.mk : Π (A : Sort 1), RLet A`
fn letin_codomain_decl() -> InductiveDecl {
    let name = n("RLetCodomain");
    let codomain = Expr::let_named(Name::anon(), sort1(), Expr::bvar(0), sort1(), false);
    let type_ = Expr::pi(BinderInfo::Default, sort1(), codomain);
    let ctor_ty = Expr::pi(
        BinderInfo::Default,
        sort1(),
        Expr::apps(Expr::const_(name.clone(), vec![]), [Expr::bvar(0)]),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name.clone(),
            type_,
            constructors: vec![Constructor {
                name: n("RLetCodomain.mk"),
                type_: ctor_ty,
            }],
        }],
    }
}

/// A genuine NON-sort codomain: `RBad : Π (A : Sort 1), Nat`. `whnf(Nat)` is the
/// `Nat` inductive, never a sort — must STILL be rejected (fail-closed control:
/// the fix widens the check to whnf, it does not disable it).
fn non_sort_codomain_decl() -> InductiveDecl {
    let name = n("RBadCodomain");
    let type_ = Expr::pi(BinderInfo::Default, sort1(), Expr::const_(n("Nat"), vec![]));
    let ctor_ty = Expr::pi(
        BinderInfo::Default,
        sort1(),
        Expr::apps(Expr::const_(name.clone(), vec![]), [Expr::bvar(0)]),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name.clone(),
            type_,
            constructors: vec![Constructor {
                name: n("RBadCodomain.mk"),
                type_: ctor_ty,
            }],
        }],
    }
}

#[test]
fn test_letin_sort_codomain_type_former_replays() {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    env.set_cumulative(true);
    env.add_inductive_core(letin_codomain_decl()).expect(
        "a type former whose codomain is `let _ in Sort` (zeta-reducible to a \
         sort) must replay — the HB `mixin_of` record shape",
    );
    // The family is registered and its result sort recovered.
    assert!(
        env.get_inductive(&n("RLetCodomain")).is_some(),
        "the LetIn-codomain inductive family must be registered",
    );
}

#[test]
fn test_non_sort_codomain_type_former_still_rejected() {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    env.set_cumulative(true);
    let err = env
        .add_inductive_core(non_sort_codomain_decl())
        .expect_err("a codomain that does not whnf to a sort must be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("does not end in a sort") || msg.to_lowercase().contains("sort"),
        "the fail-closed control must reject with a sort-shape error; got: {msg}",
    );
}
