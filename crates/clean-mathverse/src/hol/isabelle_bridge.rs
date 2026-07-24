// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-lane **connective-iso bridge library** + **syntax-directed composer**.
//!
//! Production machinery for the pilot documented in
//! [`docs/analysis/zproof-crosslane-bridge.md`](../../../../docs/analysis/zproof-crosslane-bridge.md).
//!
//! ## The problem
//!
//! The Isabelle/HOL importer embeds the object-logic connectives as
//! **impredicative (Church)** `Prop` encodings (the exact bodies
//! [`super::isabelle_pure_translate::connective_encoding`] registers), while the
//! Lean 4 / Mathlib lane spells the same theorems with the **inductive**
//! `And`/`Or`/`Exists`, the reducible `Not`, and `Iff`. An Isabelle statement
//! whose Mathlib counterpart is already Clean-`KernelVerified` is therefore NOT
//! syntactically equal — nor definitionally equal — to that counterpart, even
//! though the two are logically the same theorem.
//!
//! ## The two layers built here
//!
//! 1. **Connective-iso library** ([`iso_lemmas`]) — a bounded set of
//!    kernel-proven, foundational-closure (`⊆ FOUNDATIONAL_AXIOMS`) equivalences,
//!    one per HOL logical-signature connective:
//!    `isaTrue↔True`, `isaFalse↔False`, `isaNot↔Not`, `isaConj↔And`,
//!    `isaDisj↔Or`, `isaImp↔(→)`, `isaAll↔∀`, `isaEx↔Exists`, and the
//!    `Eq Prop ↔ Iff` carrier shim. Each is a reusable [`Expr`] constructor whose
//!    proof term the kernel re-checks.
//!
//! 2. **Syntax-directed composer** ([`compose_bridge`]) — given an
//!    Isabelle-embedded Clean statement and a Mathlib-side Clean statement that
//!    share a propositional / first-order skeleton, it walks the Mathlib side and
//!    recursively composes the iso lemmas (under `Iff` congruences) into a single
//!    whole-statement `isa ↔ mathlib` bridge term. It **declines honestly**
//!    (`Err(BridgeError::…)`) on carrier-type mismatches (`Set`/`Nat`/order towers
//!    are out of scope) rather than emitting an unsound or ill-typed term.
//!
//! ## Soundness
//!
//! Every bridge term this module emits is intended to be `add_decl`-checked by the
//! Clean kernel at the call site; a mis-shaped composition is a **kernel
//! rejection**, never a silent pass. The composer additionally structurally
//! declines known-out-of-scope node kinds up front. The intended discharge tier is
//! `KernelBridged` — *distinct* from native `KernelVerified` (see the module doc
//! in `docs/analysis/zproof-crosslane-bridge.md` and the `KernelBridged` design
//! note): the bridge is kernel-checked and foundational, the Mathlib constant is
//! Clean-KV, so the Isabelle statement is Clean-provable *by composition*.

use clean_kernel::expr::ExprKind;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

// ---------------------------------------------------------------------------
// FVarId range discipline (no collisions across the three coexisting namespaces)
//
//   * caller atoms          : ids the CALLER puts on free Prop/type variables.
//                             Keep these SMALL (below `COMPOSER_BASE`).
//   * composer binder ids   : [COMPOSER_BASE, IL_BASE) — drawn from a counter as
//                             the composer opens ∀-binders during recursion.
//   * iso/combinator ids    : [IL_BASE, ..) — used only INSIDE closed sub-terms
//                             (every one is abstracted before the term escapes),
//                             so reusing the same constant across combinators is
//                             safe. They must merely stay disjoint from any id
//                             that can be *free* in a combinator argument, i.e.
//                             disjoint from the atom + composer ranges — which
//                             `IL_BASE` guarantees.
// ---------------------------------------------------------------------------

const COMPOSER_BASE: u64 = 0x2000_0000;
const IL_BASE: u64 = 0x9000_0000;

// ---------------------------------------------------------------------------
// Term builders (fresh-fvar HOAS). Each abstracts its own fvar immediately, so a
// returned sub-term is closed in that fvar.
// ---------------------------------------------------------------------------

fn lam(ty: Expr, id: u64, f: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let body = f(Expr::fvar(fv));
    Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(fv))
}

fn pi(ty: Expr, id: u64, f: impl FnOnce(Expr) -> Expr) -> Expr {
    let fv = FVarId::new(id);
    let body = f(Expr::fvar(fv));
    Expr::pi(BinderInfo::Default, ty, body.abstract_fvar(fv))
}

fn lamp(id: u64, f: impl FnOnce(Expr) -> Expr) -> Expr {
    lam(Expr::prop(), id, f)
}

fn pip(id: u64, f: impl FnOnce(Expr) -> Expr) -> Expr {
    pi(Expr::prop(), id, f)
}

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::arrow(a, b)
}

fn obj_level() -> Level {
    Level::succ(Level::zero())
}

// --- Mathlib (inductive) spellings ---------------------------------------------

fn m_and(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("And"), [p, q])
}
fn m_or(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("Or"), [p, q])
}
fn m_not(p: Expr) -> Expr {
    Expr::app(c("Not"), p)
}
fn m_iff(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("Iff"), [p, q])
}
fn m_true() -> Expr {
    c("True")
}
fn m_false() -> Expr {
    c("False")
}

fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    Expr::apps(c("And.intro"), [p, q, hp, hq])
}
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.left"), [p, q, h])
}
fn and_right(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.right"), [p, q, h])
}
fn or_inl(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(c("Or.inl"), [p, q, h])
}
fn or_inr(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(c("Or.inr"), [p, q, h])
}
fn or_rec(a: Expr, b: Expr, motive: Expr, ml: Expr, mr: Expr, t: Expr) -> Expr {
    Expr::apps(c("Or.rec"), [a, b, motive, ml, mr, t])
}
fn iff_intro(p: Expr, q: Expr, mp: Expr, mpr: Expr) -> Expr {
    Expr::apps(c("Iff.intro"), [p, q, mp, mpr])
}
/// `@Iff.mp {a b} (h : a ↔ b) (x : a) : b` (implicits supplied positionally).
fn iff_mp(a: Expr, b: Expr, h: Expr, x: Expr) -> Expr {
    Expr::apps(c("Iff.mp"), [a, b, h, x])
}
/// `@Iff.mpr {a b} (h : a ↔ b) (x : b) : a`.
fn iff_mpr(a: Expr, b: Expr, h: Expr, x: Expr) -> Expr {
    Expr::apps(c("Iff.mpr"), [a, b, h, x])
}
/// `@Iff.trans {a b c} (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c`.
fn iff_trans(a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(c("Iff.trans"), [a, b, cc, h1, h2])
}
/// `@Iff.rfl {a} : a ↔ a`.
fn iff_rfl(a: Expr) -> Expr {
    Expr::apps(c("Iff.rfl"), [a])
}
/// `@False.elim.{0} C h : C`.
fn false_elim(cc: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("False.elim", vec![Level::zero()]),
        [cc, h],
    )
}
/// `@Eq.mp.{0} A B heq h : B`.
fn eq_mp(a: Expr, b: Expr, heq: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
        [a, b, heq, h],
    )
}
/// `@Eq.mpr.{0} A B heq h : A`.
fn eq_mpr(a: Expr, b: Expr, heq: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.mpr", vec![Level::zero()]),
        [a, b, heq, h],
    )
}
/// `@Eq.{1} Prop a b` — HOL bool-equality as the importer embeds it.
fn eq_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [Expr::prop(), a, b],
    )
}
/// `@Eq.refl.{1} ty a : @Eq ty a a`.
fn eq_refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [ty, a],
    )
}
/// `@propext {a b} (h : a ↔ b) : a = b` (foundational axiom).
fn propext(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("propext"), [a, b, h])
}

// --- Isabelle (impredicative) embeddings ---------------------------------------

/// `isaTrue ≡ ((λx:Prop. x) = (λx:Prop. x))`.
fn isa_true() -> Expr {
    let id = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [arrow(Expr::prop(), Expr::prop()), id.clone(), id],
    )
}
/// `isaFalse ≡ ∀ (R : Prop), R`.
fn isa_false() -> Expr {
    pip(IL_BASE + 0xF0, |r| r)
}
/// `isaNot P ≡ P → isaFalse`.
fn isa_not(p: Expr) -> Expr {
    arrow(p, isa_false())
}
/// `isaConj P Q ≡ ∀ (C : Prop), (P → Q → C) → C`.
fn isa_conj(p: Expr, q: Expr) -> Expr {
    pip(IL_BASE + 0xC0, move |cc| {
        arrow(arrow(p, arrow(q, cc.clone())), cc)
    })
}
/// `isaDisj P Q ≡ ∀ (C : Prop), (P → C) → (Q → C) → C`.
fn isa_disj(p: Expr, q: Expr) -> Expr {
    pip(IL_BASE + 0xD0, move |cc| {
        arrow(arrow(p, cc.clone()), arrow(arrow(q, cc.clone()), cc))
    })
}
/// `isaEx α p ≡ ∀ (Q : Prop), (∀ (x : α), p x → Q) → Q`.
fn isa_ex(alpha: Expr, p: Expr) -> Expr {
    pip(IL_BASE + 0xE0, move |q| {
        let inner = pi(alpha.clone(), IL_BASE + 0xE1, {
            let (p, q) = (p.clone(), q.clone());
            move |x| arrow(Expr::app(p, x), q)
        });
        arrow(inner, q)
    })
}

// ---------------------------------------------------------------------------
// Iso proof primitives (applied, parametric in the sub-props). Each returns the
// raw `Iff.intro …` proof of the applied iso; every closure is empty except the
// `Eq Prop ↔ Iff` shim (`propext`, foundational).
// ---------------------------------------------------------------------------

/// `isaConj P Q ↔ And P Q`.
fn proof_conj_iff_and(p: Expr, q: Expr) -> Expr {
    let mp = {
        let (p, q) = (p.clone(), q.clone());
        lam(isa_conj(p.clone(), q.clone()), IL_BASE + 0x103, move |h| {
            let and_fn = {
                let (p, q) = (p.clone(), q.clone());
                lam(p.clone(), IL_BASE + 0x104, move |hp| {
                    lam(q.clone(), IL_BASE + 0x105, move |hq| {
                        and_intro(p, q, hp, hq)
                    })
                })
            };
            Expr::apps(h, [m_and(p, q), and_fn])
        })
    };
    let mpr = {
        let (p, q) = (p.clone(), q.clone());
        lam(m_and(p.clone(), q.clone()), IL_BASE + 0x106, move |hand| {
            lamp(IL_BASE + 0x107, move |cc| {
                lam(
                    arrow(p.clone(), arrow(q.clone(), cc)),
                    IL_BASE + 0x108,
                    move |k| {
                        Expr::apps(
                            k,
                            [
                                and_left(p.clone(), q.clone(), hand.clone()),
                                and_right(p, q, hand),
                            ],
                        )
                    },
                )
            })
        })
    };
    iff_intro(isa_conj(p.clone(), q.clone()), m_and(p, q), mp, mpr)
}

/// `isaDisj P Q ↔ Or P Q`.
fn proof_disj_iff_or(p: Expr, q: Expr) -> Expr {
    let mp = {
        let (p, q) = (p.clone(), q.clone());
        lam(isa_disj(p.clone(), q.clone()), IL_BASE + 0x203, move |h| {
            let k1 = {
                let (p, q) = (p.clone(), q.clone());
                lam(p.clone(), IL_BASE + 0x204, move |hp| or_inl(p, q, hp))
            };
            let k2 = {
                let (p, q) = (p.clone(), q.clone());
                lam(q.clone(), IL_BASE + 0x205, move |hq| or_inr(p, q, hq))
            };
            Expr::apps(h, [m_or(p, q), k1, k2])
        })
    };
    let mpr = {
        let (p, q) = (p.clone(), q.clone());
        lam(m_or(p.clone(), q.clone()), IL_BASE + 0x206, move |hor| {
            lamp(IL_BASE + 0x207, move |cc| {
                let (p, q, cc2) = (p.clone(), q.clone(), cc.clone());
                lam(arrow(p.clone(), cc.clone()), IL_BASE + 0x208, move |k1| {
                    lam(arrow(q.clone(), cc2.clone()), IL_BASE + 0x209, move |k2| {
                        let motive = lam(m_or(p.clone(), q.clone()), IL_BASE + 0x210, move |_o| {
                            cc2.clone()
                        });
                        let ml = lam(p.clone(), IL_BASE + 0x211, move |hp| Expr::app(k1, hp));
                        let mr = lam(q.clone(), IL_BASE + 0x212, move |hq| Expr::app(k2, hq));
                        or_rec(p, q, motive, ml, mr, hor)
                    })
                })
            })
        })
    };
    iff_intro(isa_disj(p.clone(), q.clone()), m_or(p, q), mp, mpr)
}

/// `isaNot P ↔ Not P`.
fn proof_not_iff_not(p: Expr) -> Expr {
    let mp = {
        let p = p.clone();
        lam(isa_not(p.clone()), IL_BASE + 0x303, move |h| {
            lam(p, IL_BASE + 0x304, move |hp| {
                Expr::app(Expr::app(h, hp), m_false())
            })
        })
    };
    let mpr = {
        let p = p.clone();
        lam(m_not(p.clone()), IL_BASE + 0x305, move |h| {
            lam(p, IL_BASE + 0x306, move |hp| {
                lamp(IL_BASE + 0x307, move |rr| false_elim(rr, Expr::app(h, hp)))
            })
        })
    };
    iff_intro(isa_not(p.clone()), m_not(p), mp, mpr)
}

/// `isaTrue ↔ True`.
fn proof_true_iff_true() -> Expr {
    let mp = lam(isa_true(), IL_BASE + 0x501, |_h| c("True.intro"));
    let mpr = lam(m_true(), IL_BASE + 0x502, |_h| {
        let id = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        eq_refl(arrow(Expr::prop(), Expr::prop()), id)
    });
    iff_intro(isa_true(), m_true(), mp, mpr)
}

/// `isaFalse ↔ False`.
fn proof_false_iff_false() -> Expr {
    let mp = lam(isa_false(), IL_BASE + 0x601, |h| Expr::app(h, m_false()));
    let mpr = lam(m_false(), IL_BASE + 0x602, |h| {
        lamp(IL_BASE + 0x603, move |rr| false_elim(rr, h.clone()))
    });
    iff_intro(isa_false(), m_false(), mp, mpr)
}

/// `isaEx α p ↔ @Exists.{u} α p`, where `u` is the universe level of `α`.
fn proof_ex_iff_exists(alpha: Expr, p: Expr, u: Level) -> Expr {
    let exists_c = Expr::const_str_levels("Exists", vec![u.clone()]);
    let exists_intro = Expr::const_str_levels("Exists.intro", vec![u.clone()]);
    let exists_rec = Expr::const_str_levels("Exists.rec", vec![u]);
    let ex = Expr::apps(exists_c, [alpha.clone(), p.clone()]);

    let mp = {
        let (alpha, p, ex, exists_intro) =
            (alpha.clone(), p.clone(), ex.clone(), exists_intro.clone());
        lam(
            isa_ex(alpha.clone(), p.clone()),
            IL_BASE + 0x701,
            move |h| {
                let k = lam(alpha.clone(), IL_BASE + 0x702, {
                    let (alpha, p, exists_intro) = (alpha.clone(), p.clone(), exists_intro.clone());
                    move |x| {
                        lam(
                            Expr::app(p.clone(), x.clone()),
                            IL_BASE + 0x703,
                            move |hx| Expr::apps(exists_intro, [alpha, p, x, hx]),
                        )
                    }
                });
                Expr::apps(h, [ex, k])
            },
        )
    };
    let mpr = {
        let (alpha, p, ex, exists_rec) = (alpha.clone(), p.clone(), ex.clone(), exists_rec);
        lam(ex.clone(), IL_BASE + 0x704, move |he| {
            lamp(IL_BASE + 0x705, {
                let (alpha, p, ex, exists_rec) =
                    (alpha.clone(), p.clone(), ex.clone(), exists_rec.clone());
                move |q| {
                    let inner_ty = pi(alpha.clone(), IL_BASE + 0x706, {
                        let (p, q) = (p.clone(), q.clone());
                        move |x| arrow(Expr::app(p, x), q)
                    });
                    lam(inner_ty, IL_BASE + 0x707, {
                        let (alpha, p, ex, exists_rec, q) = (
                            alpha.clone(),
                            p.clone(),
                            ex.clone(),
                            exists_rec.clone(),
                            q.clone(),
                        );
                        move |k| {
                            let motive = lam(ex.clone(), IL_BASE + 0x708, move |_o| q.clone());
                            let minor = lam(alpha.clone(), IL_BASE + 0x709, {
                                let (p, k) = (p.clone(), k.clone());
                                move |x| {
                                    lam(Expr::app(p, x.clone()), IL_BASE + 0x70A, move |hx| {
                                        Expr::apps(k, [x, hx])
                                    })
                                }
                            });
                            Expr::apps(exists_rec, [alpha, p, motive, minor, he.clone()])
                        }
                    })
                }
            })
        })
    };
    iff_intro(isa_ex(alpha, p), ex, mp, mpr)
}

// ---------------------------------------------------------------------------
// Iff congruence combinators (given sub-`Iff`s, produce the node `Iff`). Empty
// closure; built only from `Iff.mp`/`Iff.mpr`/`Iff.intro` + the constructor
// eliminators. Directionality: first operand is the Isabelle sub-term, second the
// Mathlib sub-term, `h : isa ↔ ml`.
// ---------------------------------------------------------------------------

/// From `h : p ↔ p2`, build `Not p ↔ Not p2`.
fn not_congr(p: Expr, p2: Expr, h: Expr) -> Expr {
    let mp = {
        let (p, p2, h) = (p.clone(), p2.clone(), h.clone());
        lam(m_not(p.clone()), IL_BASE + 0x801, move |hnp| {
            lam(p2.clone(), IL_BASE + 0x802, move |hp2| {
                Expr::app(hnp, iff_mpr(p, p2, h, hp2))
            })
        })
    };
    let mpr = {
        let (p, p2, h) = (p.clone(), p2.clone(), h.clone());
        lam(m_not(p2.clone()), IL_BASE + 0x803, move |hnp2| {
            lam(p.clone(), IL_BASE + 0x804, move |hp| {
                Expr::app(hnp2, iff_mp(p, p2, h, hp))
            })
        })
    };
    iff_intro(m_not(p), m_not(p2), mp, mpr)
}

/// From `hp : p ↔ p2`, `hq : q ↔ q2`, build `And p q ↔ And p2 q2`.
fn and_congr(p: Expr, p2: Expr, q: Expr, q2: Expr, hp: Expr, hq: Expr) -> Expr {
    let mp = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_and(p.clone(), q.clone()), IL_BASE + 0x811, move |h| {
            let l = iff_mp(
                p.clone(),
                p2.clone(),
                hp,
                and_left(p.clone(), q.clone(), h.clone()),
            );
            let r = iff_mp(q.clone(), q2.clone(), hq, and_right(p, q, h));
            and_intro(p2, q2, l, r)
        })
    };
    let mpr = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_and(p2.clone(), q2.clone()), IL_BASE + 0x812, move |h| {
            let l = iff_mpr(
                p.clone(),
                p2.clone(),
                hp,
                and_left(p2.clone(), q2.clone(), h.clone()),
            );
            let r = iff_mpr(q.clone(), q2.clone(), hq, and_right(p2, q2, h));
            and_intro(p, q, l, r)
        })
    };
    iff_intro(m_and(p, q), m_and(p2, q2), mp, mpr)
}

/// From `hp : p ↔ p2`, `hq : q ↔ q2`, build `Or p q ↔ Or p2 q2`. The underlying
/// `Iff`s are oriented `isa ↔ ml`, so the forward direction transports with
/// `Iff.mp` and the backward with `Iff.mpr`.
fn or_congr(p: Expr, p2: Expr, q: Expr, q2: Expr, hp: Expr, hq: Expr) -> Expr {
    let mp = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_or(p.clone(), q.clone()), IL_BASE + 0x821, move |h| {
            let motive = lam(m_or(p.clone(), q.clone()), IL_BASE + 0x822, {
                let (p2, q2) = (p2.clone(), q2.clone());
                move |_o| m_or(p2, q2)
            });
            let ml = lam(p.clone(), IL_BASE + 0x823, {
                let (p, p2, q2, hp) = (p.clone(), p2.clone(), q2.clone(), hp.clone());
                move |hpp| or_inl(p2.clone(), q2, iff_mp(p, p2, hp, hpp))
            });
            let mr = lam(q.clone(), IL_BASE + 0x824, {
                let (q, p2, q2, hq) = (q.clone(), p2.clone(), q2.clone(), hq.clone());
                move |hqq| or_inr(p2, q2.clone(), iff_mp(q, q2, hq, hqq))
            });
            or_rec(p, q, motive, ml, mr, h)
        })
    };
    let mpr = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_or(p2.clone(), q2.clone()), IL_BASE + 0x826, move |h| {
            let motive = lam(m_or(p2.clone(), q2.clone()), IL_BASE + 0x827, {
                let (p, q) = (p.clone(), q.clone());
                move |_o| m_or(p, q)
            });
            let ml = lam(p2.clone(), IL_BASE + 0x828, {
                let (p, p2, q, hp) = (p.clone(), p2.clone(), q.clone(), hp.clone());
                move |hpp| or_inl(p.clone(), q, iff_mpr(p, p2, hp, hpp))
            });
            let mr = lam(q2.clone(), IL_BASE + 0x829, {
                let (p, q, q2, hq) = (p.clone(), q.clone(), q2.clone(), hq.clone());
                move |hqq| or_inr(p, q.clone(), iff_mpr(q, q2, hq, hqq))
            });
            or_rec(p2, q2, motive, ml, mr, h)
        })
    };
    iff_intro(m_or(p, q), m_or(p2, q2), mp, mpr)
}

/// From `hp : p ↔ p2`, `hq : q ↔ q2`, build `(p → q) ↔ (p2 → q2)`.
fn imp_congr(p: Expr, p2: Expr, q: Expr, q2: Expr, hp: Expr, hq: Expr) -> Expr {
    let mp = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(arrow(p.clone(), q.clone()), IL_BASE + 0x831, move |f| {
            lam(p2.clone(), IL_BASE + 0x832, move |hp2| {
                let arg = iff_mpr(p.clone(), p2.clone(), hp.clone(), hp2);
                iff_mp(q.clone(), q2.clone(), hq.clone(), Expr::app(f, arg))
            })
        })
    };
    let mpr = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(arrow(p2.clone(), q2.clone()), IL_BASE + 0x833, move |g| {
            lam(p.clone(), IL_BASE + 0x834, move |hp_| {
                let arg = iff_mp(p.clone(), p2.clone(), hp.clone(), hp_);
                iff_mpr(q.clone(), q2.clone(), hq.clone(), Expr::app(g, arg))
            })
        })
    };
    iff_intro(arrow(p, q), arrow(p2, q2), mp, mpr)
}

/// From `hp : p ↔ p2`, `hq : q ↔ q2`, build `(Iff p q) ↔ (Iff p2 q2)`.
fn iff_congr(p: Expr, p2: Expr, q: Expr, q2: Expr, hp: Expr, hq: Expr) -> Expr {
    let mp = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_iff(p.clone(), q.clone()), IL_BASE + 0x841, move |h| {
            let fwd = lam(p2.clone(), IL_BASE + 0x842, {
                let (p, p2, q, q2, h, hp, hq) = (
                    p.clone(),
                    p2.clone(),
                    q.clone(),
                    q2.clone(),
                    h.clone(),
                    hp.clone(),
                    hq.clone(),
                );
                move |hp2| {
                    let in_p = iff_mpr(p.clone(), p2, hp, hp2);
                    let in_q = iff_mp(p, q.clone(), h, in_p);
                    iff_mp(q, q2, hq, in_q)
                }
            });
            let bwd = lam(q2.clone(), IL_BASE + 0x843, {
                let (p, p2, q, q2, h, hp, hq) = (p, p2.clone(), q, q2.clone(), h, hp, hq);
                move |hq2| {
                    let in_q = iff_mpr(q.clone(), q2, hq, hq2);
                    let in_p = iff_mpr(p.clone(), q, h, in_q);
                    iff_mp(p, p2.clone(), hp, in_p)
                }
            });
            iff_intro(p2, q2, fwd, bwd)
        })
    };
    let mpr = {
        let (p, p2, q, q2, hp, hq) = (
            p.clone(),
            p2.clone(),
            q.clone(),
            q2.clone(),
            hp.clone(),
            hq.clone(),
        );
        lam(m_iff(p2.clone(), q2.clone()), IL_BASE + 0x844, move |h| {
            let fwd = lam(p.clone(), IL_BASE + 0x845, {
                let (p, p2, q, q2, h, hp, hq) = (
                    p.clone(),
                    p2.clone(),
                    q.clone(),
                    q2.clone(),
                    h.clone(),
                    hp.clone(),
                    hq.clone(),
                );
                move |hp_| {
                    let in_p2 = iff_mp(p, p2.clone(), hp, hp_);
                    let in_q2 = iff_mp(p2, q2.clone(), h, in_p2);
                    iff_mpr(q, q2, hq, in_q2)
                }
            });
            let bwd = lam(q.clone(), IL_BASE + 0x846, {
                let (p, p2, q, q2, h, hp, hq) = (
                    p.clone(),
                    p2.clone(),
                    q.clone(),
                    q2.clone(),
                    h.clone(),
                    hp.clone(),
                    hq.clone(),
                );
                move |hq_| {
                    let in_q2 = iff_mp(q, q2.clone(), hq, hq_);
                    let in_p2 = iff_mpr(p2.clone(), q2, h, in_q2);
                    iff_mpr(p, p2, hp, in_p2)
                }
            });
            iff_intro(p, q, fwd, bwd)
        })
    };
    iff_intro(m_iff(p.clone(), q.clone()), m_iff(p2, q2), mp, mpr)
}

/// The `Eq Prop ↔ Iff` carrier shim: `(@Eq Prop p q) ↔ (p ↔ q)`. Uses `propext`
/// (foundational) in the `mpr` direction and `Eq.mp`/`Eq.mpr` in the `mp`
/// direction.
fn eqprop_iff_iff(p: Expr, q: Expr) -> Expr {
    let mp = {
        let (p, q) = (p.clone(), q.clone());
        lam(eq_prop(p.clone(), q.clone()), IL_BASE + 0x901, move |heq| {
            let fwd = lam(p.clone(), IL_BASE + 0x902, {
                let (p, q, heq) = (p.clone(), q.clone(), heq.clone());
                move |hp| eq_mp(p, q, heq, hp)
            });
            let bwd = lam(q.clone(), IL_BASE + 0x903, {
                let (p, q, heq) = (p.clone(), q.clone(), heq.clone());
                move |hq| eq_mpr(p, q, heq, hq)
            });
            iff_intro(p, q, fwd, bwd)
        })
    };
    let mpr = {
        let (p, q) = (p.clone(), q.clone());
        lam(m_iff(p.clone(), q.clone()), IL_BASE + 0x904, move |hiff| {
            propext(p, q, hiff)
        })
    };
    iff_intro(eq_prop(p.clone(), q.clone()), m_iff(p, q), mp, mpr)
}

/// `forall_congr`: from a carrier type `t` and a per-element proof term
/// `hbody : ∀ (x : t), isa_body[x] ↔ ml_body[x]`, build
/// `(∀ x : t, isa_body[x]) ↔ (∀ x : t, ml_body[x])`.
///
/// `isa_all` / `ml_all` are the two closed `Pi` types (bodies over de-Bruijn 0);
/// `x_id`/`f_id`/`g_id` are three DISTINCT free ids the caller reserves. The
/// per-element expressions are recovered by instantiating the `Pi` bodies with a
/// fresh fvar `x`.
fn forall_congr(
    t: Expr,
    isa_all: Expr,
    ml_all: Expr,
    hbody: Expr,
    x_id: u64,
    fg_base: u64,
) -> Expr {
    // isa_all = Pi(_, t, isa_body); ml_all = Pi(_, t, ml_body).
    let (isa_body, ml_body) = match (isa_all.kind(), ml_all.kind()) {
        (ExprKind::Pi(_, _, ib), ExprKind::Pi(_, _, mb)) => ((**ib).clone(), (**mb).clone()),
        _ => unreachable!("forall_congr requires two Pi types"),
    };
    let x = Expr::fvar(FVarId::new(x_id));
    let isa_bx = isa_body.instantiate(&x);
    let ml_bx = ml_body.instantiate(&x);

    let mk = |all_from: Expr, mp: bool, f_id: u64| {
        let (t, isa_bx, ml_bx, hbody, x) = (
            t.clone(),
            isa_bx.clone(),
            ml_bx.clone(),
            hbody.clone(),
            x.clone(),
        );
        lam(all_from, f_id, move |f| {
            let inner = {
                let hbx = Expr::app(hbody.clone(), x.clone());
                let fx = Expr::app(f, x.clone());
                if mp {
                    iff_mp(isa_bx.clone(), ml_bx.clone(), hbx, fx)
                } else {
                    iff_mpr(isa_bx.clone(), ml_bx.clone(), hbx, fx)
                }
            };
            Expr::lam(
                BinderInfo::Default,
                t.clone(),
                inner.abstract_fvar(FVarId::new(x_id)),
            )
        })
    };
    let mp = mk(isa_all.clone(), true, fg_base);
    let mpr = mk(ml_all.clone(), false, fg_base + 1);
    iff_intro(isa_all, ml_all, mp, mpr)
}

// ---------------------------------------------------------------------------
// The connective-iso library (public catalogue).
// ---------------------------------------------------------------------------

/// One kernel-proven connective iso: a closed, universally-quantified equivalence
/// between the Isabelle impredicative embedding and the Mathlib inductive
/// spelling. Both `type_` and `value` are raw kernel terms; `add_decl`-checking a
/// `Declaration::Theorem { type_, value, .. }` re-verifies it, and its transitive
/// axiom closure is `⊆ FOUNDATIONAL_AXIOMS`.
#[derive(Clone)]
pub struct IsoLemma {
    /// Stable declaration name for the iso.
    pub name: &'static str,
    /// The equivalence statement (a `∀`-closed `Iff` / carrier proposition).
    pub type_: Expr,
    /// The kernel-checkable proof term.
    pub value: Expr,
}

/// `isaTrue ↔ True`.
#[must_use]
pub fn iso_true() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.true_iff_true",
        type_: m_iff(isa_true(), m_true()),
        value: proof_true_iff_true(),
    }
}

/// `isaFalse ↔ False`.
#[must_use]
pub fn iso_false() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.false_iff_false",
        type_: m_iff(isa_false(), m_false()),
        value: proof_false_iff_false(),
    }
}

/// `∀ (P : Prop), isaNot P ↔ Not P`.
#[must_use]
pub fn iso_not() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.not_iff_not",
        type_: pip(1, |p| m_iff(isa_not(p.clone()), m_not(p))),
        value: lamp(1, proof_not_iff_not),
    }
}

/// `∀ (P Q : Prop), isaConj P Q ↔ And P Q`.
#[must_use]
pub fn iso_conj() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.conj_iff_and",
        type_: pip(1, |p| {
            pip(2, move |q| {
                m_iff(isa_conj(p.clone(), q.clone()), m_and(p, q))
            })
        }),
        value: lamp(1, |p| lamp(2, move |q| proof_conj_iff_and(p, q))),
    }
}

/// `∀ (P Q : Prop), isaDisj P Q ↔ Or P Q`.
#[must_use]
pub fn iso_disj() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.disj_iff_or",
        type_: pip(1, |p| {
            pip(2, move |q| {
                m_iff(isa_disj(p.clone(), q.clone()), m_or(p, q))
            })
        }),
        value: lamp(1, |p| lamp(2, move |q| proof_disj_iff_or(p, q))),
    }
}

/// `∀ (P Q : Prop), (P → Q) ↔ (P → Q)` — the Isabelle `HOL.implies` embedding IS
/// the clean arrow, so the iso is reflexivity (documents the identity mapping).
#[must_use]
pub fn iso_imp() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.imp_iff_imp",
        type_: pip(1, |p| {
            pip(2, move |q| m_iff(arrow(p.clone(), q.clone()), arrow(p, q)))
        }),
        value: lamp(1, |p| lamp(2, move |q| iff_rfl(arrow(p, q)))),
    }
}

/// `∀ (α : Type) (p : α → Prop), (∀ x, p x) ↔ (∀ x, p x)` — the Isabelle `HOL.All`
/// embedding IS the clean `Pi`, so the iso is reflexivity.
#[must_use]
pub fn iso_all() -> IsoLemma {
    let ty_type = Expr::type_();
    let pred_ty = |a: Expr| arrow(a, Expr::prop());
    let forall_pa =
        |a: Expr, p: Expr| Expr::pi(BinderInfo::Default, a, Expr::app(p, Expr::bvar(0)));
    IsoLemma {
        name: "isa_bridge.all_iff_all",
        type_: pi(ty_type.clone(), 1, {
            let (pred_ty, forall_pa) = (pred_ty, forall_pa);
            move |a| {
                pi(pred_ty(a.clone()), 2, move |p| {
                    m_iff(forall_pa(a.clone(), p.clone()), forall_pa(a.clone(), p))
                })
            }
        }),
        value: lam(ty_type, 1, move |a| {
            lam(pred_ty(a.clone()), 2, move |p| {
                iff_rfl(forall_pa(a.clone(), p))
            })
        }),
    }
}

/// `∀ (α : Type) (p : α → Prop), isaEx α p ↔ @Exists α p`.
#[must_use]
pub fn iso_ex() -> IsoLemma {
    let ty_type = Expr::type_();
    let pred_ty = |a: Expr| arrow(a, Expr::prop());
    // α : Type = Sort 1, so the Exists universe level is 1.
    let u = obj_level();
    IsoLemma {
        name: "isa_bridge.ex_iff_exists",
        type_: pi(ty_type.clone(), 1, {
            let (pred_ty, u) = (pred_ty, u.clone());
            move |a| {
                pi(pred_ty(a.clone()), 2, {
                    let u = u.clone();
                    move |p| {
                        let ex = Expr::apps(
                            Expr::const_str_levels("Exists", vec![u.clone()]),
                            [a.clone(), p.clone()],
                        );
                        m_iff(isa_ex(a.clone(), p), ex)
                    }
                })
            }
        }),
        value: lam(ty_type, 1, move |a| {
            lam(pred_ty(a.clone()), 2, {
                let u = u.clone();
                move |p| proof_ex_iff_exists(a.clone(), p, u.clone())
            })
        }),
    }
}

/// `∀ (P Q : Prop), (@Eq Prop P Q) ↔ (P ↔ Q)` — the `Eq Prop ↔ Iff` carrier shim.
#[must_use]
pub fn iso_eqprop_iff() -> IsoLemma {
    IsoLemma {
        name: "isa_bridge.eqprop_iff_iff",
        type_: pip(1, |p| {
            pip(2, move |q| {
                m_iff(eq_prop(p.clone(), q.clone()), m_iff(p, q))
            })
        }),
        value: lamp(1, |p| lamp(2, move |q| eqprop_iff_iff(p, q))),
    }
}

/// The full connective-iso library: one kernel-proven, foundational iso per HOL
/// logical-signature connective. Bounded by the HOL signature.
#[must_use]
pub fn iso_lemmas() -> Vec<IsoLemma> {
    vec![
        iso_true(),
        iso_false(),
        iso_not(),
        iso_conj(),
        iso_disj(),
        iso_imp(),
        iso_all(),
        iso_ex(),
        iso_eqprop_iff(),
    ]
}

// ---------------------------------------------------------------------------
// The syntax-directed composer.
// ---------------------------------------------------------------------------

/// Why a whole-statement bridge could not be composed. Each variant is an
/// *honest decline* — the composer never emits an unsound term instead.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BridgeError {
    /// A Mathlib node kind is outside the composer's propositional / first-order
    /// scope (e.g. `Exists`, or a `Set`/`Nat`/order carrier operator).
    #[error("node kind out of scope for the connective-iso composer: {0}")]
    OutOfScope(&'static str),
    /// An operand sits in a proposition slot but is a sort/type — a carrier
    /// mismatch (`Set`/`Nat`/order towers are out of scope per the pilot).
    #[error("carrier-type mismatch: a type/sort appears where a proposition is required")]
    CarrierMismatch,
    /// The provided Isabelle embedding does not match the embedding implied by the
    /// Mathlib skeleton — the two statements are not the same theorem under the
    /// importer's encoding.
    #[error("isabelle embedding does not match the mathlib skeleton")]
    IsaMismatch,
}

struct Composer {
    next: u64,
}

impl Composer {
    fn fresh(&mut self) -> u64 {
        let id = self.next;
        self.next += 1;
        id
    }

    /// Recurse over the Mathlib term `ml`; return `(isa_expected, proof)` where
    /// `proof : isa_expected ↔ ml` and `isa_expected` is the Isabelle embedding
    /// implied by `ml`'s skeleton.
    fn go(&mut self, ml: &Expr) -> Result<(Expr, Expr), BridgeError> {
        let ml = ml.strip_mdata();
        if let ExprKind::Pi(_, dom, cod) = ml.kind() {
            let dom = (**dom).clone();
            let cod = (**cod).clone();
            if cod.has_loose_bvar(0) {
                return self.forall_node(dom, cod, ml);
            }
            return self.imp_node(dom, cod);
        }

        let head = ml.get_app_fn();
        if let ExprKind::Const(name, _levels) = head.kind() {
            let args: Vec<Expr> = ml.get_app_args().iter().map(|a| (*a).clone()).collect();
            match (name.to_string().as_str(), args.len()) {
                ("Not", 1) => return self.not_node(&args[0]),
                ("And", 2) => return self.bin_node(Conn::And, &args[0], &args[1]),
                ("Or", 2) => return self.bin_node(Conn::Or, &args[0], &args[1]),
                ("Iff", 2) => return self.iff_node(&args[0], &args[1]),
                ("Exists", _) => return Err(BridgeError::OutOfScope("Exists")),
                ("True", 0) => return Ok((isa_true(), proof_true_iff_true())),
                ("False", 0) => return Ok((isa_false(), proof_false_iff_false())),
                _ => {}
            }
        }
        self.atom(ml)
    }

    fn atom(&self, ml: &Expr) -> Result<(Expr, Expr), BridgeError> {
        if ml.is_sort() {
            return Err(BridgeError::CarrierMismatch);
        }
        Ok((ml.clone(), iff_rfl(ml.clone())))
    }

    fn not_node(&mut self, a: &Expr) -> Result<(Expr, Expr), BridgeError> {
        let (ia, pa) = self.go(a)?;
        let isa = isa_not(ia.clone());
        let proof = iff_trans(
            isa_not(ia.clone()),
            m_not(ia.clone()),
            m_not(a.clone()),
            proof_not_iff_not(ia.clone()),
            not_congr(ia, a.clone(), pa),
        );
        Ok((isa, proof))
    }

    fn bin_node(&mut self, conn: Conn, a: &Expr, b: &Expr) -> Result<(Expr, Expr), BridgeError> {
        let (ia, pa) = self.go(a)?;
        let (ib, pb) = self.go(b)?;
        match conn {
            Conn::And => {
                let isa = isa_conj(ia.clone(), ib.clone());
                let step1 = proof_conj_iff_and(ia.clone(), ib.clone());
                let step2 = and_congr(ia.clone(), a.clone(), ib.clone(), b.clone(), pa, pb);
                let proof = iff_trans(
                    isa.clone(),
                    m_and(ia, ib),
                    m_and(a.clone(), b.clone()),
                    step1,
                    step2,
                );
                Ok((isa, proof))
            }
            Conn::Or => {
                let isa = isa_disj(ia.clone(), ib.clone());
                let step1 = proof_disj_iff_or(ia.clone(), ib.clone());
                let step2 = or_congr(ia.clone(), a.clone(), ib.clone(), b.clone(), pa, pb);
                let proof = iff_trans(
                    isa.clone(),
                    m_or(ia, ib),
                    m_or(a.clone(), b.clone()),
                    step1,
                    step2,
                );
                Ok((isa, proof))
            }
        }
    }

    fn iff_node(&mut self, a: &Expr, b: &Expr) -> Result<(Expr, Expr), BridgeError> {
        let (ia, pa) = self.go(a)?;
        let (ib, pb) = self.go(b)?;
        let isa = eq_prop(ia.clone(), ib.clone());
        let step1 = eqprop_iff_iff(ia.clone(), ib.clone());
        let step2 = iff_congr(ia.clone(), a.clone(), ib.clone(), b.clone(), pa, pb);
        let proof = iff_trans(
            isa.clone(),
            m_iff(ia, ib),
            m_iff(a.clone(), b.clone()),
            step1,
            step2,
        );
        Ok((isa, proof))
    }

    fn imp_node(&mut self, dom: Expr, cod: Expr) -> Result<(Expr, Expr), BridgeError> {
        let (id_, pd) = self.go(&dom)?;
        let (ic, pc) = self.go(&cod)?;
        let isa = arrow(id_.clone(), ic.clone());
        let proof = imp_congr(id_, dom, ic, cod, pd, pc);
        Ok((isa, proof))
    }

    fn forall_node(&mut self, t: Expr, cod: Expr, ml: &Expr) -> Result<(Expr, Expr), BridgeError> {
        let x_id = self.fresh();
        let cod_open = cod.instantiate(&Expr::fvar(FVarId::new(x_id)));
        let (isa_body_open, proof_open) = self.go(&cod_open)?;
        let isa_all = Expr::pi(
            BinderInfo::Default,
            t.clone(),
            isa_body_open.abstract_fvar(FVarId::new(x_id)),
        );
        let ml_all = ml.clone();
        let hbody = Expr::lam(
            BinderInfo::Default,
            t.clone(),
            proof_open.abstract_fvar(FVarId::new(x_id)),
        );
        let fg_base = self.fresh();
        let _ = self.fresh(); // reserve fg_base + 1
        let proof = forall_congr(t, isa_all.clone(), ml_all, hbody, x_id, fg_base);
        Ok((isa_all, proof))
    }
}

enum Conn {
    And,
    Or,
}

// ---------------------------------------------------------------------------
// Isabelle-side pre-normalization: δ-unfold the importer's connective definition
// consts to the impredicative encodings the composer walks.
// ---------------------------------------------------------------------------

/// Fresh-fvar id base for binder descent during [`normalize_isa_connectives`].
/// Disjoint from the caller-atom range (kept small), [`COMPOSER_BASE`], and
/// [`IL_BASE`]; every id is abstracted away before the normalized term is
/// returned, so it can never escape or collide with a live free variable.
const NORM_BASE: u64 = 0x4000_0000;

/// The Isabelle connective **definition consts** the importer's `embed_term`
/// emits for `HOL.conj`/`disj`/`Not`/`True`/`False`, plus the
/// `Code_Generator.holds` alias of `True` — see
/// `super::isabelle_pure_translate::connective_def_name`. Each is a reducible
/// clean `Definition` whose body IS the impredicative encoding this module builds,
/// so a fully-applied occurrence δ-unfolds to the matching `isa_*` constructor.
/// Returns `None` for any other head (or a wrong arity), leaving the generic
/// structural rebuild to handle it.
fn unfold_connective_def_const(name: &str, args: &[Expr], next: &mut u64) -> Option<Expr> {
    match (name, args.len()) {
        ("isabelle.def.HOL.True" | "isabelle.def.Code_Generator.holds", 0) => Some(isa_true()),
        ("isabelle.def.HOL.False", 0) => Some(isa_false()),
        ("isabelle.def.HOL.Not", 1) => Some(isa_not(normalize_rec(&args[0], next))),
        ("isabelle.def.HOL.conj", 2) => Some(isa_conj(
            normalize_rec(&args[0], next),
            normalize_rec(&args[1], next),
        )),
        ("isabelle.def.HOL.disj", 2) => Some(isa_disj(
            normalize_rec(&args[0], next),
            normalize_rec(&args[1], next),
        )),
        _ => None,
    }
}

/// δ-unfold the Isabelle **connective definition consts** the importer's
/// `embed_term` emits — `isabelle.def.HOL.{True,False,Not,conj,disj}` and
/// `isabelle.def.Code_Generator.holds` — into the impredicative (Church) `Prop`
/// encodings (`isaTrue`/`isaFalse`/`isaNot`/`isaConj`/`isaDisj`) that
/// [`compose_bridge`] walks.
///
/// A real corpus line spells its embedded statement with these def-consts (each a
/// clean `Definition` whose value IS the impredicative encoding — see
/// `connective_encoding` / `connective_definition_decls`), whereas the composer
/// builds the impredicative encoding directly. The two spellings are
/// **definitionally equal** (the def-consts are reducible and δ-unfold to the
/// encoding), so normalizing one to the other is sound — and the kernel re-check
/// of the final bridge term remains the arbiter: a wrong normalization produces a
/// term the kernel rejects, never a silent pass. This lets a JSON-driven dependent
/// feed the composer the encoding it expects (the composer itself is untouched).
///
/// Non-connective structure (`Eq`, `→`, `∀`, `∃`, atoms, sorts) is preserved
/// verbatim — those already match the composer's spellings — while binders are
/// descended through with a fresh fvar (opened, normalized, re-abstracted) so that
/// a connective unfolded under a binder never captures a loose de-Bruijn variable.
/// On an already-impredicative statement (no def-consts) this is the identity.
pub(crate) fn normalize_isa_connectives(isa: &Expr) -> Expr {
    let mut next = NORM_BASE;
    normalize_rec(isa, &mut next)
}

fn normalize_rec(e: &Expr, next: &mut u64) -> Expr {
    let e = e.strip_mdata();
    let head = e.get_app_fn();
    let args: Vec<Expr> = e.get_app_args().iter().map(|a| (*a).clone()).collect();

    // Connective def-const spine → unfold to the impredicative builder. `head` is
    // the bare const (arity 0) for a nullary `True`/`False`.
    if let ExprKind::Const(name, _) = head.kind() {
        if let Some(unfolded) = unfold_connective_def_const(&name.to_string(), &args, next) {
            return unfolded;
        }
    }

    // Non-connective application spine: rebuild verbatim, recursing into head +
    // operands to reach connectives nested arbitrarily deep.
    if !args.is_empty() {
        let f = normalize_rec(head, next);
        let normed: Vec<Expr> = args.iter().map(|a| normalize_rec(a, next)).collect();
        return Expr::apps(f, normed);
    }

    // Leaf / binder. Descend under a binder through a fresh fvar so an unfolded
    // connective can never capture the binder's loose bvar; the open/abstract pair
    // round-trips, so this is the identity on binder structure.
    match e.kind() {
        ExprKind::Pi(bd, ty, body) => {
            let fv = FVarId::new(*next);
            *next += 1;
            let ty_n = normalize_rec(ty, next);
            let body_n = normalize_rec(&body.instantiate(&Expr::fvar(fv)), next);
            Expr::pi(*bd, ty_n, body_n.abstract_fvar(fv))
        }
        ExprKind::Lam(bd, ty, body) => {
            let fv = FVarId::new(*next);
            *next += 1;
            let ty_n = normalize_rec(ty, next);
            let body_n = normalize_rec(&body.instantiate(&Expr::fvar(fv)), next);
            Expr::lam(*bd, ty_n, body_n.abstract_fvar(fv))
        }
        _ => e.clone(),
    }
}

/// Compose a whole-statement `isa ↔ mathlib` bridge from the connective-iso
/// library, driven by the shared propositional / first-order skeleton.
///
/// `isa` is an Isabelle-embedded Clean proposition; `mathlib` is the Mathlib-side
/// Clean proposition (inductive connectives, `Iff`). The Isabelle side is
/// **pre-normalized** ([`normalize_isa_connectives`]) so that a real corpus line —
/// whose connectives are spelled with the importer's reducible definition consts
/// (`isabelle.def.HOL.conj` …) — matches the impredicative (Church) encoding the
/// composer walks; a hand-built raw-encoding statement normalizes to itself. On
/// success the returned term proves `normalize(isa) ↔ mathlib` (definitionally
/// `isa ↔ mathlib`, the def-consts being reducible) and is intended to be
/// `add_decl`-checked by the caller (a mis-shaped composition is a kernel
/// rejection, never a silent pass).
///
/// # Errors
///
/// Returns [`BridgeError`] when the skeleton contains an out-of-scope node
/// (`Exists`, carrier towers), a proposition slot holds a type, or the provided
/// Isabelle embedding does not match the embedding implied by the Mathlib
/// skeleton.
pub fn compose_bridge(isa: &Expr, mathlib: &Expr) -> Result<Expr, BridgeError> {
    let mut composer = Composer {
        next: COMPOSER_BASE,
    };
    let (isa_expected, proof) = composer.go(mathlib)?;
    if isa_expected != normalize_isa_connectives(isa) {
        return Err(BridgeError::IsaMismatch);
    }
    Ok(proof)
}

/// **The KernelBridged discharge term.** Given an Isabelle-embedded statement
/// `isa`, a Mathlib-KV constant's statement type `mathlib_type`, and a reference
/// term `mathlib_ref` to that constant (its `KernelVerified` witness, e.g.
/// `Const "not_and_or"`), compose the connective bridge and return the closed
/// proof term
///
/// ```text
///   @Iff.mpr isa mathlib_type (bridge : isa ↔ mathlib_type) (mathlib_ref : mathlib_type)
///     : isa
/// ```
///
/// This is a **real Clean proof of the Isabelle statement**: the composer's
/// `bridge` has a foundational-only axiom closure, and `mathlib_ref` is the
/// Mathlib constant's own kernel-checked value, so the whole term's closure is
/// the union of the two (still foundational when the Mathlib constant is
/// `KernelVerified`). The caller is expected to `add_decl`
/// `Declaration::Theorem { type_: isa, value: <this term>, .. }` — a mis-shaped
/// composition is a kernel rejection, never a silent pass — and to assert the
/// transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS` before minting the
/// [`crate::types::ImportConfidence::KernelBridged`] verdict.
///
/// # Errors
///
/// Returns [`BridgeError`] when [`compose_bridge`] declines (out-of-scope node,
/// carrier mismatch, or the provided `isa` embedding does not match the Mathlib
/// skeleton).
pub fn discharge_value(
    isa: &Expr,
    mathlib_type: &Expr,
    mathlib_ref: Expr,
) -> Result<Expr, BridgeError> {
    let bridge = compose_bridge(isa, mathlib_type)?;
    Ok(iff_mpr(
        isa.clone(),
        mathlib_type.clone(),
        bridge,
        mathlib_ref,
    ))
}

#[cfg(test)]
mod tests;
