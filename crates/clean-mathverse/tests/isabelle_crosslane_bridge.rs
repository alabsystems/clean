// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-lane bridge pilot: kernel-checked, foundational-closure equivalence
//! between the Isabelle/HOL importer's *impredicative* connective embedding and
//! the Lean4/Mathlib *inductive* connectives.
//!
//! ## Why this test exists
//!
//! The cross-lane synergy thesis is: an Isabelle statement whose Mathlib
//! counterpart is already Clean-`KernelVerified` can be discharged by a small
//! **kernel-checked bridge** proven in Clean — no external prover, foundational
//! closure preserved. The overlap survey (`docs/analysis/zproof-crosslane-bridge.md`)
//! found the cleanest hit is Isabelle `de_Morgan_conj`
//! (`¬(P ∧ Q) = (¬P ∨ ¬Q)`) ↔ Mathlib `not_and_or`
//! (`¬(a ∧ b) ↔ ¬a ∨ ¬b`), which lives in the reproducible KV slice
//! (`Mathlib/Logic/Basic`).
//!
//! The two Clean spellings are NOT syntactically equal and NOT defeq. The
//! Isabelle importer embeds the object-logic connectives as impredicative
//! (Church) `Prop` encodings — the exact bodies registered by
//! `clean_mathverse::hol::…::connectives::connective_encoding`:
//!
//! ```text
//!   isaFalse    ≡  ∀ (R : Prop), R
//!   isaNot  P   ≡  P → isaFalse
//!   isaConj P Q ≡  ∀ (C : Prop), (P → Q → C) → C
//!   isaDisj P Q ≡  ∀ (C : Prop), (P → C) → (Q → C) → C
//!   HOL.eq @bool → @Eq Prop            (propositional equality, NOT `Iff`)
//! ```
//!
//! Mathlib spells the same theorem with the *inductive* `And`/`Or`, the reducible
//! `Not`, and `Iff`. The gap therefore has three independent layers: (1) the
//! truth carrier `Eq Prop` vs `Iff`; (2) impredicative vs inductive connectives
//! (only *propositionally* — never definitionally — equal); (3) congruence
//! composition across the connective positions.
//!
//! This pilot constructs, as raw kernel proof terms, and `add_decl`-checks:
//!   * `bridge_isa_conj_iff_and` — `isaConj P Q ↔ And P Q`
//!   * `bridge_isa_disj_iff_or`  — `isaDisj P Q ↔ Or  P Q`
//!   * `bridge_isa_not_iff_not`  — `isaNot P   ↔ Not P`
//!   * `bridge_de_morgan`        — the full capstone: from the Isabelle-embedded
//!     `Eq Prop` statement of `de_Morgan_conj`, derive the Mathlib
//!     `not_and_or` `Iff`.
//!
//! Every declaration is required to kernel-check AND to have a transitive axiom
//! closure ⊆ `FOUNDATIONAL_AXIOMS` (here the closure is in fact empty — the
//! connective isos need no axiom at all; the capstone uses only `Eq.mp`/`Eq.mpr`,
//! which are axiom-free). This is the honest evidence that the encoding gap is
//! bridgeable by a real, foundational, kernel-checked proof.

use clean_kernel::{
    is_foundational_axiom, BinderInfo, Declaration, Environment, Expr, FVarId, Level, Name,
};

// ---------------------------------------------------------------------------
// Term builders (fresh-fvar HOAS; every binder abstracts its own fvar before
// composition, so a returned sub-term is closed and ids may be reused across
// sibling closed sub-terms — only simultaneously-free binders need distinct ids).
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

// --- Mathlib (inductive) side --------------------------------------------------

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
fn iff_intro(p: Expr, q: Expr, mp: Expr, mpr: Expr) -> Expr {
    Expr::apps(c("Iff.intro"), [p, q, mp, mpr])
}
/// `@False.elim.{0} C h : C`  (C implicit but supplied positionally).
fn false_elim(cc: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("False.elim", vec![Level::zero()]),
        [cc, h],
    )
}
/// `@Or.rec {a b} {motive} minor_l minor_r t`  (Prop-recursor, no level param).
fn or_rec(a: Expr, b: Expr, motive: Expr, ml: Expr, mr: Expr, t: Expr) -> Expr {
    Expr::apps(c("Or.rec"), [a, b, motive, ml, mr, t])
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
/// `@Eq.{1} Prop a b`  — HOL bool-equality as the importer embeds it.
fn eq_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [Expr::prop(), a, b],
    )
}

// --- Isabelle (impredicative) side ---------------------------------------------

/// `isaFalse ≡ ∀ (R : Prop), R`.
fn isa_false() -> Expr {
    pip(0xF0, |r| r)
}
/// `isaNot P ≡ P → isaFalse`.
fn isa_not(p: Expr) -> Expr {
    arrow(p, isa_false())
}
/// `isaConj P Q ≡ ∀ (C : Prop), (P → Q → C) → C`.
fn isa_conj(p: Expr, q: Expr) -> Expr {
    pip(0xC0, move |cc| arrow(arrow(p, arrow(q, cc.clone())), cc))
}
/// `isaDisj P Q ≡ ∀ (C : Prop), (P → C) → (Q → C) → C`.
fn isa_disj(p: Expr, q: Expr) -> Expr {
    pip(0xD0, move |cc| {
        arrow(arrow(p, cc.clone()), arrow(arrow(q, cc.clone()), cc))
    })
}

// ---------------------------------------------------------------------------
// Environment + foundational-closure assertion
// ---------------------------------------------------------------------------

fn base_env() -> Environment {
    let mut env = Environment::with_prelude();
    // Idempotent: guarantees Or / Or.rec are present regardless of prelude order.
    env.init_or().expect("init_or");
    env
}

fn add_theorem(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: Vec::new(),
        type_,
        value,
    })
    .unwrap_or_else(|e| panic!("kernel rejected `{name}`: {e:?}"));

    // Foundational closure: every axiom in the transitive closure must be in
    // FOUNDATIONAL_AXIOMS (propext / Quot.sound / Classical.choice / Eq builtins).
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("no axiom_deps for `{name}`"));
    let non_foundational: Vec<String> = deps
        .iter()
        .filter(|n| !is_foundational_axiom(n))
        .map(ToString::to_string)
        .collect();
    assert!(
        non_foundational.is_empty(),
        "`{name}` has non-foundational axioms in its closure: {non_foundational:?}"
    );
}

// ---------------------------------------------------------------------------
// The three connective-iso bridge primitives.
// ---------------------------------------------------------------------------

#[test]
fn test_bridge_isa_conj_iff_and() {
    let mut env = base_env();

    // ∀ (P Q : Prop), isaConj P Q ↔ And P Q
    let ty = pip(101, |p| {
        pip(102, move |q| {
            m_iff(isa_conj(p.clone(), q.clone()), m_and(p, q))
        })
    });

    let value = lamp(101, |p| {
        lamp(102, move |q| {
            // mp : isaConj P Q → And P Q
            //    = fun h => h (And P Q) (fun hp hq => And.intro P Q hp hq)
            let mp = {
                let (p, q) = (p.clone(), q.clone());
                lam(isa_conj(p.clone(), q.clone()), 103, move |h| {
                    let and_fn = {
                        let (p, q) = (p.clone(), q.clone());
                        lam(p.clone(), 104, move |hp| {
                            lam(q.clone(), 105, move |hq| and_intro(p, q, hp, hq))
                        })
                    };
                    Expr::apps(h, [m_and(p, q), and_fn])
                })
            };
            // mpr : And P Q → isaConj P Q
            //     = fun hand => fun C k => k (And.left P Q hand) (And.right P Q hand)
            let mpr = {
                let (p, q) = (p.clone(), q.clone());
                lam(m_and(p.clone(), q.clone()), 106, move |hand| {
                    lamp(107, move |cc| {
                        lam(arrow(p.clone(), arrow(q.clone(), cc)), 108, move |k| {
                            Expr::apps(
                                k,
                                [
                                    and_left(p.clone(), q.clone(), hand.clone()),
                                    and_right(p, q, hand),
                                ],
                            )
                        })
                    })
                })
            };
            iff_intro(isa_conj(p.clone(), q.clone()), m_and(p, q), mp, mpr)
        })
    });

    add_theorem(&mut env, "bridge_isa_conj_iff_and", ty, value);
}

#[test]
fn test_bridge_isa_disj_iff_or() {
    let mut env = base_env();

    let ty = pip(201, |p| {
        pip(202, move |q| {
            m_iff(isa_disj(p.clone(), q.clone()), m_or(p, q))
        })
    });

    let value = lamp(201, |p| {
        lamp(202, move |q| {
            // mp : isaDisj P Q → Or P Q
            //    = fun h => h (Or P Q) (fun hp => Or.inl ..) (fun hq => Or.inr ..)
            let mp = {
                let (p, q) = (p.clone(), q.clone());
                lam(isa_disj(p.clone(), q.clone()), 203, move |h| {
                    let k1 = {
                        let (p, q) = (p.clone(), q.clone());
                        lam(p.clone(), 204, move |hp| or_inl(p, q, hp))
                    };
                    let k2 = {
                        let (p, q) = (p.clone(), q.clone());
                        lam(q.clone(), 205, move |hq| or_inr(p, q, hq))
                    };
                    Expr::apps(h, [m_or(p, q), k1, k2])
                })
            };
            // mpr : Or P Q → isaDisj P Q
            //     = fun hor => fun C k1 k2 => Or.rec (fun _ => C) (fun hp => k1 hp)
            //                                        (fun hq => k2 hq) hor
            let mpr = {
                let (p, q) = (p.clone(), q.clone());
                lam(m_or(p.clone(), q.clone()), 206, move |hor| {
                    lamp(207, move |cc| {
                        let (p, q, cc2) = (p.clone(), q.clone(), cc.clone());
                        lam(arrow(p.clone(), cc.clone()), 208, move |k1| {
                            lam(arrow(q.clone(), cc2.clone()), 209, move |k2| {
                                let motive =
                                    lam(m_or(p.clone(), q.clone()), 210, move |_o| cc2.clone());
                                let ml = lam(p.clone(), 211, move |hp| Expr::app(k1, hp));
                                let mr = lam(q.clone(), 212, move |hq| Expr::app(k2, hq));
                                or_rec(p, q, motive, ml, mr, hor)
                            })
                        })
                    })
                })
            };
            iff_intro(isa_disj(p.clone(), q.clone()), m_or(p, q), mp, mpr)
        })
    });

    add_theorem(&mut env, "bridge_isa_disj_iff_or", ty, value);
}

#[test]
fn test_bridge_isa_not_iff_not() {
    let mut env = base_env();

    let ty = pip(301, |p| m_iff(isa_not(p.clone()), m_not(p)));

    let value = lamp(301, |p| {
        // mp : isaNot P → Not P  = fun h hp => (h hp) False
        let mp = {
            let p = p.clone();
            lam(isa_not(p.clone()), 303, move |h| {
                lam(p, 304, move |hp| Expr::app(Expr::app(h, hp), m_false()))
            })
        };
        // mpr : Not P → isaNot P  = fun h hp R => False.elim R (h hp)
        let mpr = {
            let p = p.clone();
            lam(m_not(p.clone()), 305, move |h| {
                lam(p, 306, move |hp| {
                    lamp(307, move |rr| false_elim(rr, Expr::app(h, hp)))
                })
            })
        };
        iff_intro(isa_not(p.clone()), m_not(p), mp, mpr)
    });

    add_theorem(&mut env, "bridge_isa_not_iff_not", ty, value);
}

// ---------------------------------------------------------------------------
// The capstone: the full de_Morgan_conj ↔ not_and_or bridge.
//
//   ∀ (P Q : Prop),
//     (@Eq Prop (isaNot (isaConj P Q)) (isaDisj (isaNot P) (isaNot Q)))   -- Isabelle
//       → (Not (And P Q) ↔ Or (Not P) (Not Q))                            -- Mathlib
// ---------------------------------------------------------------------------

#[test]
fn test_bridge_de_morgan_capstone() {
    let mut env = base_env();

    // A = isaNot (isaConj P Q) ; B = isaDisj (isaNot P) (isaNot Q)
    let a_of = |p: Expr, q: Expr| isa_not(isa_conj(p, q));
    let b_of = |p: Expr, q: Expr| isa_disj(isa_not(p), isa_not(q));

    let ty = pip(400, |p| {
        pip(401, move |q| {
            let eqab = eq_prop(a_of(p.clone(), q.clone()), b_of(p.clone(), q.clone()));
            let concl = m_iff(
                m_not(m_and(p.clone(), q.clone())),
                m_or(m_not(p.clone()), m_not(q)),
            );
            arrow(eqab, concl)
        })
    });

    let value = lamp(400, |p| {
        lamp(401, move |q| {
            let eqab = eq_prop(a_of(p.clone(), q.clone()), b_of(p.clone(), q.clone()));
            lam(eqab, 402, move |heq| {
                let a = a_of(p.clone(), q.clone());
                let b = b_of(p.clone(), q.clone());

                // FWD : Not (And P Q) → Or (Not P) (Not Q)
                let fwd = {
                    let (p, q, a, b, heq) =
                        (p.clone(), q.clone(), a.clone(), b.clone(), heq.clone());
                    lam(m_not(m_and(p.clone(), q.clone())), 410, move |hn| {
                        // hisaL : isaNot (isaConj P Q)
                        //  = fun hc => fun R => False.elim R (hn (hc (And P Q) and_fn))
                        let hisa_l = {
                            let (p, q) = (p.clone(), q.clone());
                            lam(isa_conj(p.clone(), q.clone()), 411, move |hc| {
                                let and_fn = {
                                    let (p, q) = (p.clone(), q.clone());
                                    lam(p.clone(), 413, move |hp| {
                                        lam(q.clone(), 414, move |hq| and_intro(p, q, hp, hq))
                                    })
                                };
                                let and_pq = Expr::apps(hc, [m_and(p.clone(), q.clone()), and_fn]);
                                lamp(412, move |rr| {
                                    false_elim(rr, Expr::app(hn.clone(), and_pq.clone()))
                                })
                            })
                        };
                        // hisaR : isaDisj (isaNot P) (isaNot Q)  via Eq.mp heq
                        let hisa_r = eq_mp(a.clone(), b.clone(), heq.clone(), hisa_l);
                        // eliminate isaDisj into Or (Not P) (Not Q)
                        let k1 = {
                            let (p, q) = (p.clone(), q.clone());
                            lam(isa_not(p.clone()), 415, move |x| {
                                let np = lam(p.clone(), 416, move |hp| {
                                    Expr::app(Expr::app(x, hp), m_false())
                                });
                                or_inl(m_not(p.clone()), m_not(q.clone()), np)
                            })
                        };
                        let k2 = {
                            let (p, q) = (p.clone(), q.clone());
                            lam(isa_not(q.clone()), 417, move |y| {
                                let nq = lam(q.clone(), 418, move |hq| {
                                    Expr::app(Expr::app(y, hq), m_false())
                                });
                                or_inr(m_not(p.clone()), m_not(q.clone()), nq)
                            })
                        };
                        Expr::apps(hisa_r, [m_or(m_not(p.clone()), m_not(q.clone())), k1, k2])
                    })
                };

                // BWD : Or (Not P) (Not Q) → Not (And P Q)
                let bwd = {
                    let (p, q, a, b, heq) =
                        (p.clone(), q.clone(), a.clone(), b.clone(), heq.clone());
                    lam(m_or(m_not(p.clone()), m_not(q.clone())), 420, move |hor| {
                        // hisaR' : isaDisj (isaNot P) (isaNot Q)
                        //  = fun C k1 k2 => Or.rec (fun _ => C)
                        //       (fun np => k1 (fun hp R => False.elim R (np hp)))
                        //       (fun nq => k2 (fun hq R => False.elim R (nq hq))) hor
                        let hisa_r = {
                            let (p, q) = (p.clone(), q.clone());
                            lamp(421, move |cc| {
                                let (p, q, cc2) = (p.clone(), q.clone(), cc.clone());
                                lam(arrow(isa_not(p.clone()), cc.clone()), 422, move |k1| {
                                    let (p, q, cc3) = (p.clone(), q.clone(), cc2.clone());
                                    lam(arrow(isa_not(q.clone()), cc2.clone()), 423, move |k2| {
                                        let motive = lam(
                                            m_or(m_not(p.clone()), m_not(q.clone())),
                                            424,
                                            move |_o| cc3.clone(),
                                        );
                                        let ml = {
                                            let p = p.clone();
                                            lam(m_not(p.clone()), 425, move |np| {
                                                let isanp = lam(p.clone(), 426, move |hp| {
                                                    lamp(427, move |rr| {
                                                        false_elim(
                                                            rr,
                                                            Expr::app(np.clone(), hp.clone()),
                                                        )
                                                    })
                                                });
                                                Expr::app(k1, isanp)
                                            })
                                        };
                                        let mr = {
                                            let q = q.clone();
                                            lam(m_not(q.clone()), 428, move |nq| {
                                                let isanq = lam(q.clone(), 429, move |hq| {
                                                    lamp(430, move |rr| {
                                                        false_elim(
                                                            rr,
                                                            Expr::app(nq.clone(), hq.clone()),
                                                        )
                                                    })
                                                });
                                                Expr::app(k2, isanq)
                                            })
                                        };
                                        or_rec(
                                            m_not(p.clone()),
                                            m_not(q.clone()),
                                            motive,
                                            ml,
                                            mr,
                                            hor.clone(),
                                        )
                                    })
                                })
                            })
                        };
                        // hisaL' : isaNot (isaConj P Q)  via Eq.mpr heq
                        let hisa_l = eq_mpr(a.clone(), b.clone(), heq.clone(), hisa_r);
                        // build Not (And P Q) = And P Q → False
                        lam(m_and(p.clone(), q.clone()), 431, move |hand| {
                            let conj_fn = {
                                let (p, q) = (p.clone(), q.clone());
                                lamp(432, move |cc| {
                                    lam(arrow(p.clone(), arrow(q.clone(), cc)), 433, move |k| {
                                        Expr::apps(
                                            k,
                                            [
                                                and_left(p.clone(), q.clone(), hand.clone()),
                                                and_right(p, q, hand),
                                            ],
                                        )
                                    })
                                })
                            };
                            Expr::app(Expr::app(hisa_l.clone(), conj_fn), m_false())
                        })
                    })
                };

                iff_intro(
                    m_not(m_and(p.clone(), q.clone())),
                    m_or(m_not(p.clone()), m_not(q)),
                    fwd,
                    bwd,
                )
            })
        })
    });

    add_theorem(&mut env, "bridge_de_morgan", ty, value);
}
