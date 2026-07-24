// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;

/// The master inversion's honest residual axiom closure: EMPTY. The
/// KernelInferResult un-Skolemization retired the LAST infer-band skolem — the
/// inferred subtypes Rf/Ra are bound existentially inside AppInferDecomp (the
/// app payload) and the app constructor. The pi domain/codomain, lam-body-type,
/// and level Skolems (KernelInferAppPiDomain / KernelInferAppPiCodomain /
/// KernelLamBodyType / KernelLamDomainLevel / KernelPiDomainLevel /
/// KernelPiCodomainLevel) were already RETIRED into the App/Lam/PiInferWitness
/// packaged existentials, and the two vestigial binder-admissibility guards
/// KernelLamBodyAdmissible / KernelPiBodyAdmissible retired outright. Every
/// flipped per-case lemma now inherits an EMPTY residual set.
const RESIDUAL: [&str; 0] = [];

#[test]
fn test_kernel_infer_accepts_is_faithful_inductive() {
    let spec = build_spec_with_stack();

    let accepts = spec
        .definitions()
        .get("KernelInferAccepts")
        .expect("KernelInferAccepts should exist");
    assert!(
        !accepts.is_axiom,
        "KernelInferAccepts should no longer be an opaque axiom"
    );

    // One constructor per KExpr arm with a success path in the production
    // kernel's infer_type — and NO bvar constructor: the real kernel errors
    // unconditionally on BVar (tc/infer.rs BVar arm returns
    // Err(UnboundVariable); cert/infer_core.rs mirrors), so bvar acceptance
    // is uninhabited.
    assert!(
        !spec.definitions().contains_key("KernelInferAccepts.bvar"),
        "KernelInferAccepts must NOT have a bvar constructor (the kernel \
         unconditionally rejects bound variables)"
    );

    // The recorded type_src for constructors is a placeholder; the real type
    // is the elaborated Expr. Pin faithfulness on its rendered form — each
    // constructor's field must carry exactly the old per-case axiom's content,
    // THAT AXIOM'S OWN GUARD STRUCTURE INCLUDED. The const/app guard pins fail
    // closed against the Step-2 unguarded-strengthening regression (an
    // unguarded field would silently strengthen every producer axiom).
    let ctor_pins: [(&str, &[&str]); 5] = [
        ("KernelInferAccepts.sort", &["Level", "succ", "Eq"]),
        (
            "KernelInferAccepts.const",
            &[
                "KernelStateEnvValid",
                "KernelStateLocalCtxWellFormed",
                "KernelInputAdmissible",
                "has_type",
            ],
        ),
        (
            "KernelInferAccepts.app",
            &[
                "KernelInferAccepts",
                "AppInferWitness",
                "KernelStateEnvValid",
                "KernelInputAdmissible",
            ],
        ),
        ("KernelInferAccepts.lam", &["LamInferWitness"]),
        ("KernelInferAccepts.pi", &["PiInferWitness"]),
    ];
    for (ctor, pins) in ctor_pins {
        let def = spec
            .definitions()
            .get(ctor)
            .unwrap_or_else(|| panic!("{ctor} constructor should be registered"));
        assert!(
            !def.is_axiom,
            "{ctor} should be a kernel-generated constructor, not an axiom"
        );
        let ty = format!(
            "{:?}",
            def.elaborated_type
                .as_ref()
                .unwrap_or_else(|| panic!("{ctor} should record its elaborated type"))
        );
        for pinned in pins {
            assert!(
                ty.contains(pinned),
                "{ctor}'s elaborated type should reference {pinned}: {ty}"
            );
        }
    }
}

/// Permanent record of the kernel-generated recursor shape (the §1.3
/// diagnostic's answer): `st` is promoted to a uniform PARAMETER while
/// `(e, T)` remain TRUE indices — the five constructor conclusions differ in
/// the `e` position, so the recursor is the KernelWhnfAccepts.rec index-motive
/// shape (motive over both KExpr indices + the major premise), NOT the
/// param-promoted AndType.rec shape of Step 2's single-ctor KernelDefEqAccepts.
/// Minor premises follow declaration order (sort, const, app, lam, pi); the
/// app minor receives the IHs for its TWO recursive fields (Step 4 inlined the
/// argument-check content, adding the argument-infer recursive field) LAST
/// (after all fields), in field order.
#[test]
fn test_kernel_infer_accepts_recursor_is_index_shaped() {
    let spec = build_spec_with_stack();
    let rec = spec
        .definitions()
        .get("KernelInferAccepts.rec")
        .expect("KernelInferAccepts.rec should be registered");
    // Normalize the Debug rendering by dropping the (deterministic but
    // algorithm-dependent) cached_hash digits so the pin survives hash-fn or
    // cache churn while still freezing the structural shape.
    let ty = strip_hashes(&format!(
        "{:?}",
        rec.elaborated_type
            .as_ref()
            .expect("KernelInferAccepts.rec should record its elaborated type")
    ));

    // Index-motive shape: the motive binds two explicit KExpr indices and the
    // major premise KernelInferAccepts st x y (rendered with de Bruijn vars).
    let motive_shape = concat!(
        "Pi(BinderData { info: Default, mult: Many }, ",
        "Const(Name { inner: Str(Name { inner: Anon }, \"KExpr\") }, []), ",
        "Pi(BinderData { info: Default, mult: Many }, ",
        "Const(Name { inner: Str(Name { inner: Anon }, \"KExpr\") }, []), ",
        "Pi(BinderData { info: Default, mult: Many }, ",
        "App(App(App(Const(Name { inner: Str(Name { inner: Anon }, ",
        "\"KernelInferAccepts\") }, []), ",
        "BVar(2)), BVar(1)), BVar(0)), Sort(Param("
    );
    assert!(
        ty.contains(motive_shape),
        "KernelInferAccepts.rec should have the index-motive shape \
         (motive : forall (x y : KExpr), KernelInferAccepts st x y -> Sort u): {ty}"
    );

    // All five minor signatures present (each minor's conclusion applies the
    // motive to the ctor application), in declaration order: sort, const,
    // app, lam, pi — the master inversion's value is written to this order.
    let pos = |needle: &str| {
        ty.find(needle)
            .unwrap_or_else(|| panic!("recursor type should mention {needle}: {ty}"))
    };
    let sort_pos = pos("\"KernelInferAccepts\") }, \"sort\")");
    let const_pos = pos("\"KernelInferAccepts\") }, \"const\")");
    let app_pos = pos("\"KernelInferAccepts\") }, \"app\")");
    let lam_pos = pos("\"KernelInferAccepts\") }, \"lam\")");
    let pi_pos = pos("\"KernelInferAccepts\") }, \"pi\")");
    assert!(
        sort_pos < const_pos && const_pos < app_pos && app_pos < lam_pos && lam_pos < pi_pos,
        "KernelInferAccepts.rec minor premises should follow declaration order \
         sort, const, app, lam, pi: positions {sort_pos}/{const_pos}/{app_pos}/{lam_pos}/{pi_pos}"
    );

    // The app minor now binds the inferred subtypes Rf/Ra existentially (the
    // KernelInferResult un-Skolemization): the recursor no longer mentions the
    // retired KernelInferResult Skolem anywhere, and the app minor's witness
    // field is the reframed AppInferWitness (indexed by Rf/Ra).
    assert!(
        !ty.contains("\"KernelInferResult\""),
        "KernelInferAccepts.rec must no longer name the retired KernelInferResult Skolem: {ty}"
    );
    assert!(
        ty.contains("\"AppInferWitness\""),
        "the app minor should carry the reframed AppInferWitness field (indexed by Rf/Ra): {ty}"
    );

    // The lam minor now routes the lam body-TYPE through inference: the lam
    // constructor carries a RECURSIVE KernelInferAccepts st body bt premise
    // (bt bound existentially) alongside the reframed LamInferWitness (indexed
    // by A/body/bt/T), mirroring the app arm. So the lam minor receives an IH
    // for that recursive body-infer field, and the recursor mentions the
    // reframed LamInferWitness.
    assert!(
        ty.contains("\"LamInferWitness\""),
        "the lam minor should carry the reframed LamInferWitness field (indexed by A/body/bt/T): {ty}"
    );
}

/// Step 4: the faithful KernelCheckAccepts inductive replaces the opaque
/// check-side token. Single mk constructor whose two fields carry EXACTLY the
/// formerly-assumed kernel_check_decomposition pair (unguarded, as that axiom
/// was) and the formerly-assumed kernel_check_types_admissible guarded
/// implication (its guards verbatim).
#[test]
fn test_kernel_check_accepts_is_faithful_inductive() {
    let spec = build_spec_with_stack();

    let accepts = spec
        .definitions()
        .get("KernelCheckAccepts")
        .expect("KernelCheckAccepts should exist");
    assert!(
        !accepts.is_axiom,
        "KernelCheckAccepts should no longer be an opaque axiom"
    );

    let mk = spec
        .definitions()
        .get("KernelCheckAccepts.mk")
        .expect("KernelCheckAccepts.mk constructor should be registered");
    assert!(
        !mk.is_axiom,
        "KernelCheckAccepts.mk should be a kernel-generated constructor, not an axiom"
    );
    let ty = format!(
        "{:?}",
        mk.elaborated_type
            .as_ref()
            .expect("KernelCheckAccepts.mk should record its elaborated type")
    );
    // Field 1 (decomposition pair, unguarded) + field 2 (guarded
    // admissibility implication) pins. The guard pins fail closed against the
    // Step-2 unguarded-strengthening regression.
    for pinned in [
        "ProdType",
        "KernelInferAccepts",
        "KernelDefEqAccepts",
        "KernelStateEnvValid",
        "KernelStateLocalCtxWellFormed",
        "KernelInputAdmissible",
        "KernelBinaryInputAdmissible",
    ] {
        assert!(
            ty.contains(pinned),
            "KernelCheckAccepts.mk's elaborated type should reference {pinned}: {ty}"
        );
    }
    // The inferred type is now bound EXISTENTIALLY (R) — the retired
    // KernelInferResult Skolem must not appear.
    assert!(
        !ty.contains("KernelInferResult"),
        "KernelCheckAccepts.mk must no longer name the retired KernelInferResult Skolem: {ty}"
    );
}

/// Permanent record of the kernel-generated recursor shape for the Step-4
/// check inductive (the diagnostic's answer): the mk conclusion is UNIFORM in
/// (e, T), so the elaborator PROMOTES st/e/T to inductive parameters — the
/// recursor is the param-fixed AndType.rec shape (motive over the major
/// premise ONLY, one minor over the two constructor fields), exactly Step 2's
/// KernelDefEqAccepts.rec shape and NOT the index-motive shape of
/// KernelInferAccepts.rec.
#[test]
fn test_kernel_check_accepts_recursor_is_param_promoted() {
    let spec = build_spec_with_stack();
    let rec = spec
        .definitions()
        .get("KernelCheckAccepts.rec")
        .expect("KernelCheckAccepts.rec should be registered");
    let ty = strip_hashes(&format!(
        "{:?}",
        rec.elaborated_type
            .as_ref()
            .expect("KernelCheckAccepts.rec should record its elaborated type")
    ));

    // Param-promoted motive shape: the motive binds ONLY the major premise
    // KernelCheckAccepts st e T (rendered with de Bruijn vars over the three
    // promoted parameters) — no KExpr index binders inside the motive.
    let motive_shape = concat!(
        "Pi(BinderData { info: Implicit, mult: Many }, ",
        "Pi(BinderData { info: Default, mult: Many }, ",
        "App(App(App(Const(Name { inner: Str(Name { inner: Anon }, ",
        "\"KernelCheckAccepts\") }, []), ",
        "BVar(2)), BVar(1)), BVar(0)), Sort(Param("
    );
    assert!(
        ty.contains(motive_shape),
        "KernelCheckAccepts.rec should have the param-promoted motive shape \
         (motive : KernelCheckAccepts st e T -> Sort u): {ty}"
    );

    // The single minor's conclusion applies the motive to the mk application.
    assert!(
        ty.contains("\"KernelCheckAccepts\") }, \"mk\")"),
        "KernelCheckAccepts.rec's minor should conclude at the mk application: {ty}"
    );
}

/// Drop `cached_hash: <digits>` runs from a Debug rendering (the hashes are
/// deterministic per name but tied to the hash algorithm; the structural pin
/// must not depend on them).
fn strip_hashes(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find(", cached_hash: ") {
        out.push_str(&rest[..i]);
        rest = &rest[i + ", cached_hash: ".len()..];
        let end = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

#[test]
fn test_infer_band_flips_are_derived_eliminators() {
    let spec = build_spec_with_stack();

    // The six formerly-assumed per-case axioms + the master inversion + the
    // bvar-emptiness corollary: all derived, all kernel-checked at spec build.
    for (name, value_marker) in [
        ("kernel_infer_inversion", "KernelInferAccepts.rec"),
        ("kernel_infer_bvar_empty", "kernel_infer_inversion"),
        ("kernel_infer_sort_result", "kernel_infer_inversion"),
        ("kernel_infer_const_sound", "kernel_infer_inversion"),
        ("kernel_infer_app_decomposition", "kernel_infer_inversion"),
        ("kernel_infer_lam_decomposition", "kernel_infer_inversion"),
        ("kernel_infer_pi_decomposition", "kernel_infer_inversion"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should no longer be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (kernel-checked derivation)"
        );
        let value = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should carry a derivation proof term"));
        assert!(
            value.contains(value_marker),
            "{name}'s value should be derived via {value_marker}: {value}"
        );
    }

    // Guard-consumption pins (the Step-2 pattern): the guarded flips must
    // APPLY their own guard premises to the recovered guarded-implication
    // field — the old axioms' guarded strength is the trust content preserved.
    let const_sound = spec
        .definitions()
        .get("kernel_infer_const_sound")
        .expect("kernel_infer_const_sound should exist");
    assert!(
        const_sound
            .value_src
            .as_ref()
            .expect("const_sound value")
            .contains("hinfer henv hctx hadm"),
        "kernel_infer_const_sound must genuinely consume its guard premises"
    );
    // kernel_infer_app_fun_type_admissible was RETIRED by the KernelInferResult
    // un-Skolemization; the fun-type admissibility guard is now recovered directly
    // inside kernel_infer_app_sound's AppInferDecomp elimination.
    assert!(
        spec.definitions()
            .get("kernel_infer_app_fun_type_admissible")
            .is_none(),
        "kernel_infer_app_fun_type_admissible should be retired"
    );

    // The master inversion's recorded residual closure is exactly RESIDUAL (EMPTY
    // after the un-Skolemization).
    let inversion = spec
        .definitions()
        .get("kernel_infer_inversion")
        .expect("kernel_infer_inversion should exist");
    let mut sorted: Vec<&str> = inversion.axiom_deps.iter().map(String::as_str).collect();
    sorted.sort_unstable();
    assert_eq!(
        sorted,
        RESIDUAL.to_vec(),
        "kernel_infer_inversion's residual axiom closure should be EMPTY (the last \
         infer-band skolem KernelInferResult is retired)"
    );
}

#[test]
fn test_infer_skolem_witnesses_are_helper_axioms() {
    let spec = build_spec_with_stack();

    // KernelInferResult — the last infer-band skolem — is now DELETED (census
    // 13->12) by the existential reframe (Rf/Ra bound on the app ctor +
    // AppInferWitness, one shared R on KernelCheckAccepts.mk). NO infer-band
    // skolem survives; the inferred sub-results are bound existentially.
    assert!(
        spec.definitions().get("KernelInferResult").is_none(),
        "KernelInferResult should be DELETED (census 13->12 existential reframe)"
    );

    // The 8 retired Skolems must be GONE from the spec entirely — no longer any
    // definition, no longer any kernel-env axiom. This includes the two
    // vestigial binder-admissibility guards (census 18->16).
    for retired in [
        "KernelInferAppPiDomain",
        "KernelInferAppPiCodomain",
        "KernelLamBodyType",
        "KernelLamDomainLevel",
        "KernelPiDomainLevel",
        "KernelPiCodomainLevel",
        "KernelLamBodyAdmissible",
        "KernelPiBodyAdmissible",
    ] {
        assert!(
            spec.definitions().get(retired).is_none(),
            "retired Skolem {retired} must no longer be a SpecDefinition"
        );
    }

    // The 3 packaged-existential witnesses that replaced them are kernel-checked
    // inductives (NOT axioms) — the census must not grow from them.
    for name in [
        "AppInferWitness",
        "AppInferWitness.mk",
        "AppInferWitness.rec",
        "LamInferWitness",
        "LamInferWitness.mk",
        "LamInferWitness.rec",
        "PiInferWitness",
        "PiInferWitness.mk",
        "PiInferWitness.rec",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} witness inductive should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
    }
}

#[test]
fn test_kexpr_eqt_is_universe_adapter_not_axiom() {
    let spec = build_spec_with_stack();

    // KExprEqT is a kernel-checked inductive (Type-valued equality witness),
    // NOT an axiom — the ratchet census must not grow from it.
    for name in ["KExprEqT", "KExprEqT.refl", "KExprEqT.rec"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
    }

    // The sort flip converts the adapter back to the byte-identical Prop
    // equation via KExprEqT.rec + Eq.refl.
    let sort_result = spec
        .definitions()
        .get("kernel_infer_sort_result")
        .expect("kernel_infer_sort_result should exist");
    let value = sort_result.value_src.as_ref().expect("sort_result value");
    assert!(
        value.contains("KExprEqT.rec") && value.contains("Eq.refl"),
        "kernel_infer_sort_result should convert the KExprEqT adapter back to \
         the Prop equation: {value}"
    );
    assert!(
        sort_result
            .type_src
            .contains("Eq KExpr (KExpr.sort (Level.succ l)) T"),
        "kernel_infer_sort_result's TYPE must remain the byte-identical Prop \
         equation of the old axiom: {}",
        sort_result.type_src
    );
}
