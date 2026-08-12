//! The MUST-REFUSE battery.
//!
//! These land before any emitter exists, deliberately: the whole value of
//! validated recognition is that it declines impostors, and a recognizer
//! whose refusals are untested is a name match with extra steps.
//!
//! Environments are hand-built rather than elaborated, because the
//! adversarial cases -- a forged origin, a tampered corecursor, a
//! valueless constant wearing the right name -- are exactly what the
//! elaborator will not produce.

use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{BinderInfo, CodataOrigin, Declaration};

const NAT: &str = "Nat";

fn nat() -> Expr {
    Expr::const_(Name::from_string(NAT), vec![])
}

/// Register `Codata.ucorec` and a carrier's polynomial descriptor as
/// axioms, so a hand-built corecursor can carry a CANONICAL body.
///
/// The seed reserves `Codata.*` in a real environment; these tests build
/// unseeded environments precisely so they can place the pieces (and, in
/// the refusal cases, place them WRONG).
fn seed_pieces(env: &mut Environment, carrier: &str) {
    fn ax(env: &mut Environment, n: &str, ty: Expr) {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: ty,
        })
        .expect("axiom must register");
    }
    if env.get_const(&Name::from_string("Codata.ucorec")).is_none() {
        let ty = Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(BinderInfo::Default, nat(), nat()),
            ),
        );
        ax(env, "Codata.ucorec", ty);
    }
    for suffix in ["shapeF", "posF", "tgtF"] {
        let n = format!("{carrier}.{suffix}");
        if env.get_const(&Name::from_string(&n)).is_none() {
            ax(env, &n, nat());
        }
    }
}

/// The canonical body: `Codata.ucorec <C>.shapeF <C>.posF <C>.tgtF`.
fn canonical_body(carrier: &str) -> Expr {
    let d = |suffix: &str| Expr::const_(Name::from_string(&format!("{carrier}.{suffix}")), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Codata.ucorec"), vec![]),
                d("shapeF"),
            ),
            d("posF"),
        ),
        d("tgtF"),
    )
}

/// `Nat.Nat.Nat.Nat`, the corecursor's type in these fixtures.
fn corec_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(BinderInfo::Default, nat(), nat()),
        ),
    )
}

/// A corecursor with generated-shaped parameter names (two `F`-suffixed
/// field slots plus a trailing state argument -- the PLAIN lane) and the
/// given body.
fn env_with_corec_body(body: Expr, carrier: &str) -> (Environment, Name) {
    env_with_corec_body_over(body, &[carrier])
}

/// As [`env_with_corec_body`], seeding descriptors for SEVERAL carriers before
/// the corecursor is registered — needed when a body mentions more than one.
fn env_with_corec_body_over(body: Expr, carriers: &[&str]) -> (Environment, Name) {
    let mut env = Environment::with_prelude();
    for c in carriers {
        seed_pieces(&mut env, c);
    }
    // Recognition requires carrier provenance -- the `codata` command marks
    // what it generates. These environments are hand-built, so the mark is set
    // explicitly. The provenance gate has its own tests over a REAL elaborated
    // environment in clean-elab/tests/rank7_codata_recognize_e2e.rs, which is
    // where it belongs; leaving it unmarked here would only make every case in
    // this battery decline for the same uninformative reason.
    env.mark_codata_carrier(Name::from_string(NAT));
    let corec = Name::from_string("probe.corec");
    let value = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), body),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: corec.clone(),
        level_params: vec![],
        type_: corec_ty(),
        value,
        is_reducible: false,
    })
    .expect("probe corecursor must register");
    env.set_param_infos(
        corec.clone(),
        vec![
            ("valF".to_string(), BinderInfo::Default),
            ("nextF".to_string(), BinderInfo::Default),
            ("init".to_string(), BinderInfo::Default),
        ],
    );
    (env, corec)
}

/// The well-formed environment: canonical body over `Nat`'s descriptor.
fn env_with_corec() -> (Environment, Name) {
    env_with_corec_body(canonical_body(NAT), NAT)
}

fn origin(corec: &Name) -> CodataOrigin {
    CodataOrigin {
        lane: CodataLane::Plain,
        carrier: Name::from_string(NAT),
        corec: corec.clone(),
        slots: vec!["valF".to_string(), "nextF".to_string()],
    }
}

/// A saturated application `probe.corec a b c`.
fn saturated(corec: &Name, argc: usize) -> Expr {
    let mut e = Expr::const_(corec.clone(), vec![]);
    for i in 0..argc {
        e = Expr::app(e, Expr::nat_lit(i as u64));
    }
    e
}

fn def_name() -> Name {
    Name::from_string("doubler")
}

#[test]
fn recognizes_a_wellformed_corec_application() {
    let (mut env, corec) = env_with_corec();
    env.set_codata_origin(def_name(), origin(&corec));
    let got = recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3))
        .expect("a well-formed corec application must be recognized");
    assert_eq!(got.corec, corec);
    assert_eq!(got.carrier, Name::from_string(NAT));
    assert_eq!(got.slot_count, 2);
    assert_eq!(got.lane, CodataLane::Plain);
}

/// A codef WITH PARAMETERS stores `fun … => corec …`, so the application
/// sits under one lambda per parameter.
///
/// This case was missing when the battery was first written, and the
/// hand-built positive above passed happily without it -- the recognizer
/// declined every parameterized codef in existence while these tests stayed
/// green, because the battery shared the same wrong assumption. The
/// end-to-end test against a real elaborated codef is what caught it
/// (tests/rank7_codata_recognize_e2e.rs); this pins it here too.
#[test]
fn recognizes_a_corec_under_parameter_lambdas() {
    let (mut env, corec) = env_with_corec();
    env.set_codata_origin(def_name(), origin(&corec));
    let wrapped = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), saturated(&corec, 3)),
    );
    let got = recognize_codata_corec(&env, &def_name(), &wrapped)
        .expect("a corec under parameter lambdas must be recognized");
    assert_eq!(got.param_count, 2, "two parameter binders were peeled");
    assert_eq!(got.slot_count, 2);
}

/// No origin ⇒ decline. This is the case that matters most: it is what
/// stops a HAND-WRITTEN `def Stream.corec` from being treated as generated
/// codata. `C.corec` is a user-derivable name, so absence of provenance is
/// the only thing separating the two.
#[test]
fn refuses_when_no_origin_was_minted() {
    let (env, corec) = env_with_corec();
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "without a minted origin the application must NOT be recognized"
    );
}

/// A forged origin pointing at a constant that is not the applied head.
#[test]
fn refuses_when_head_is_not_the_recorded_corecursor() {
    let (mut env, corec) = env_with_corec();
    let mut o = origin(&corec);
    o.corec = Name::from_string("some.other.corec");
    env.set_codata_origin(def_name(), o);
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "head constant must be the recorded corecursor"
    );
}

/// The recorded corecursor does not resolve at all.
#[test]
fn refuses_when_the_corecursor_does_not_resolve() {
    let mut env = Environment::with_prelude();
    let ghost = Name::from_string("ghost.corec");
    env.set_codata_origin(def_name(), origin(&ghost));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&ghost, 3)).is_none(),
        "an unresolvable corecursor must be refused"
    );
}

/// A VALUELESS constant wearing the corecursor's name -- an axiom, not a
/// generated definition.
#[test]
fn refuses_a_valueless_corecursor() {
    let mut env = Environment::with_prelude();
    let corec = Name::from_string("probe.corec");
    env.add_decl(Declaration::Axiom {
        name: corec.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat(), nat()),
    })
    .expect("axiom must register");
    env.set_param_infos(
        corec.clone(),
        vec![
            ("valF".to_string(), BinderInfo::Default),
            ("nextF".to_string(), BinderInfo::Default),
            ("init".to_string(), BinderInfo::Default),
        ],
    );
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "a valueless constant is not a generated corecursor"
    );
}

/// The corecursor was re-registered with a DIFFERENT shape: its re-derived
/// slots no longer reproduce the recorded ones.
#[test]
fn refuses_a_tampered_corecursor_shape() {
    let (mut env, corec) = env_with_corec();
    env.set_param_infos(
        corec.clone(),
        vec![
            ("somethingElseF".to_string(), BinderInfo::Default),
            ("nextF".to_string(), BinderInfo::Default),
            ("init".to_string(), BinderInfo::Default),
        ],
    );
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "re-derived slots must reproduce the recorded ones"
    );
}

/// A hint whose LANE was flipped. The lane selects the canonical form
/// downstream, so it is checked against the derived shape, not trusted.
#[test]
fn refuses_a_lane_that_contradicts_the_shape() {
    let (mut env, corec) = env_with_corec();
    let mut o = origin(&corec);
    o.lane = CodataLane::Indexed; // the shape is Plain
    env.set_codata_origin(def_name(), o);
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "a lane contradicting the derived shape must be refused"
    );
}

/// A partially applied corecursor is not a corecursive VALUE.
#[test]
fn refuses_an_unsaturated_application() {
    let (mut env, corec) = env_with_corec();
    env.set_codata_origin(def_name(), origin(&corec));
    for argc in 0..=2 {
        assert!(
            recognize_codata_corec(&env, &def_name(), &saturated(&corec, argc)).is_none(),
            "an application with {argc} args (slots=2) must be refused"
        );
    }
}

/// The recorded carrier does not head the corecursor's result type.
#[test]
fn refuses_when_the_carrier_does_not_head_the_result() {
    let (mut env, corec) = env_with_corec();
    let mut o = origin(&corec);
    o.carrier = Name::from_string("Bool"); // result is Nat
    env.set_codata_origin(def_name(), o);
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "the carrier must actually head the corecursor's result type"
    );
}

/// A corecursor whose body is NOT the canonical generated form.
///
/// This is the gap B3 shipped with and B3b closes: the constant here has
/// the right type, the right parameter names, the right carrier and a
/// stored value -- it passes every identity check -- but it computes
/// something else entirely. Only replaying the body catches it.
#[test]
fn refuses_a_corecursor_whose_body_is_not_canonical() {
    // `fun _ _ c => c` -- plausible, well-typed, and not a corecursor.
    let (mut env, corec) = env_with_corec_body(Expr::bvar(0), NAT);
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "a non-canonical body must be refused even when identity checks pass"
    );
}

/// Descriptors that are MENTIONED but not in position do not satisfy replay.
///
/// The review's route: a corecursor running on a FOREIGN descriptor while the
/// carrier's own names appear somewhere harmless. The old check asked only
/// whether each descriptor was mentioned anywhere in the application, which
/// this body satisfies — every one of `Nat.shapeF`, `Nat.posF`, `Nat.tgtF`
/// occurs — while the corecursor's actual arguments are `Other`'s. The emitted
/// index would then advance per `Nat.tgtF` while the corecursor advanced per
/// `Other.tgtF`.
///
/// The descriptors must OCCUPY the generator's argument positions.
#[test]
fn refuses_descriptors_mentioned_but_not_in_position() {
    let d = |carrier: &str, suffix: &str| {
        Expr::const_(Name::from_string(&format!("{carrier}.{suffix}")), vec![])
    };
    // Nat.add <Nat descriptor> <Other descriptor> at each position: the real
    // descriptor is mentioned, but the argument is not it.
    let mixed = |suffix: &str| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                d(NAT, suffix),
            ),
            d("Other", suffix),
        )
    };
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Codata.ucorec"), vec![]),
                mixed("shapeF"),
            ),
            mixed("posF"),
        ),
        mixed("tgtF"),
    );
    let (mut env, corec) = env_with_corec_body_over(body, &["Other", NAT]);
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "descriptors must occupy the generator's positions, not merely appear"
    );
}

/// A canonical body over SOMEBODY ELSE'S descriptor.
///
/// Anchoring on the seed primitive alone would accept this: the head is a
/// genuine `Codata.ucorec`. Requiring the CARRIER's own descriptor is what
/// ties the corecursor to this specific codata type.
#[test]
fn refuses_a_canonical_body_over_a_foreign_descriptor() {
    let (mut env, corec) = env_with_corec_body(canonical_body("Other"), "Other");
    // The origin claims Nat as carrier, but the body uses Other's descriptor.
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &saturated(&corec, 3)).is_none(),
        "a corecursor over a foreign descriptor must be refused"
    );
}

/// A non-application body never recognizes.
#[test]
fn refuses_a_non_application_body() {
    let (mut env, corec) = env_with_corec();
    env.set_codata_origin(def_name(), origin(&corec));
    assert!(
        recognize_codata_corec(&env, &def_name(), &nat()).is_none(),
        "a bare constant is not a corec application"
    );
}
