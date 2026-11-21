// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Automatic ordinary-core candidates, replayed by the actual adopted checker.
//! Not full Init/C4 coverage, completeness, compiled authority or a Rust proof.
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderData, Expr, ExprKind, FVarId};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::kcheck_trace::core::advice::{produce_ordinary, produce_ordinary_with_labelled};
use clean_kernel::kcheck_trace::core::{CoreTracer, LabelledEnvironment, Refusal};
use clean_kernel::kcheck_trace::wire::{encode_frames, encode_tokens};
use clean_kernel::kcheck_trace::Token;
use clean_kernel::{Level, Name};
use clean_olean::test_support::compiled_fixture_dir;
use std::process::Command;

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderData::default(), domain, body)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderData::default(), domain, body)
}
fn let_expr(ty: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_named(Name::anon(), ty, value, body, false)
}

fn definition(name: &str, ty: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    }
}
fn theorem(name: &str, ty: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
    }
}

fn eq(level: Level, ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level]),
        [ty, left, right],
    )
}

fn refl(level: Level, ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level]),
        [ty, value],
    )
}

fn recursor_prefix_rhs(type_: &Expr, binders: usize) -> Expr {
    if binders == 0 {
        return Expr::bvar(0);
    }
    let ExprKind::Pi(binder, domain, body) = type_.kind() else {
        panic!("recursor fixture telescope ended early");
    };
    Expr::lam(
        *binder,
        domain.as_ref().clone(),
        recursor_prefix_rhs(body, binders - 1),
    )
}

fn nat_eq_fixture() -> (Environment, LabelledEnvironment) {
    let mut env = Environment::default();
    let nat_name = Name::from_string("Nat");
    let nat = Expr::const_(nat_name.clone(), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat_name,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: pi(nat.clone(), nat),
                },
            ],
        }],
    })
    .expect("native Nat fixture");
    env.init_eq().expect("native Eq fixture");
    let names = [
        "Nat", "Nat.zero", "Nat.succ", "Nat.rec", "Eq", "Eq.refl", "Eq.rec",
    ]
    .map(Name::from_string);
    let mut tracer = CoreTracer::new(&env, 1_000_000);
    let mut labelled = tracer
        .annotate_group(&names)
        .expect("labelled Nat/Eq checker prefix");
    // `Environment::init_eq` keeps placeholder binder domains in its native
    // reduction metadata, while the adopted checker stores the promoted
    // singleton rule at Eq.rec's actual telescope. Reconstruct exactly that
    // four-binder `fun ... => minor` syntax for this native interoperability
    // fixture; production imported syntax remains the required source.
    let eq_rec = env
        .get_recursor(&Name::from_string("Eq.rec"))
        .expect("Eq.rec metadata");
    let raw_rhs = recursor_prefix_rhs(&eq_rec.type_, 4);
    let mut rhs_tracer = CoreTracer::new(&env, 1_000_000);
    let (rhs, _) = rhs_tracer
        .check(&raw_rhs)
        .expect("labelled promoted Eq.rec rule");
    labelled.insert_rule(
        Name::from_string("Eq.rec"),
        Name::from_string("Eq.refl"),
        rhs,
    );
    (env, labelled)
}

fn pinned_nat_eq_fixture() -> (Environment, LabelledEnvironment) {
    let mut env = Environment::default();
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib])
        .expect("load pinned Init.Prelude");
    let names = [
        "Nat", "Nat.zero", "Nat.succ", "Nat.rec", "Eq", "Eq.refl", "Eq.rec",
    ]
    .map(Name::from_string);
    let mut tracer = CoreTracer::new(&env, 1_000_000);
    let labelled = tracer
        .annotate_group(&names)
        .expect("labelled pinned Nat/Eq checker prefix");
    (env, labelled)
}

fn rec_zero_declaration() -> Declaration {
    let one = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let motive = lam(nat.clone(), nat.clone());
    let succ_minor = lam(
        nat.clone(),
        lam(
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );
    let rec_zero = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![one.clone()]),
        [motive, zero.clone(), succ_minor, zero.clone()],
    );
    theorem(
        "recZero",
        eq(one.clone(), nat.clone(), rec_zero, zero.clone()),
        refl(one, nat, zero),
    )
}

fn rec_succ_declaration() -> Declaration {
    let one = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = |value| Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), value);
    let succ_zero = succ(zero.clone());
    let motive = lam(nat.clone(), nat.clone());
    let succ_minor = lam(nat.clone(), lam(nat.clone(), succ(Expr::bvar(0))));
    let rec_succ = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![one.clone()]),
        [motive, zero, succ_minor, succ_zero.clone()],
    );
    theorem(
        "recSucc",
        eq(one.clone(), nat.clone(), rec_succ, succ_zero.clone()),
        refl(one, nat, succ_zero),
    )
}

fn rec_k_declaration() -> Declaration {
    let one = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let eq_zz = eq(one.clone(), nat.clone(), zero.clone(), zero.clone());
    let motive = lam(
        nat.clone(),
        lam(
            eq(one.clone(), nat.clone(), zero.clone(), Expr::bvar(0)),
            nat.clone(),
        ),
    );
    let rec_k = Expr::apps(
        Expr::const_(Name::from_string("Eq.rec"), vec![one.clone(), one.clone()]),
        [
            nat.clone(),
            zero.clone(),
            motive,
            zero.clone(),
            zero.clone(),
            Expr::bvar(0),
        ],
    );
    theorem(
        "recK",
        pi(
            eq_zz.clone(),
            eq(one.clone(), nat.clone(), rec_k, zero.clone()),
        ),
        lam(eq_zz, refl(one, nat, zero)),
    )
}

fn rec_eq_declaration() -> Declaration {
    let one = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let motive = lam(
        nat.clone(),
        lam(
            eq(one.clone(), nat.clone(), zero.clone(), Expr::bvar(0)),
            nat.clone(),
        ),
    );
    let rec_eq = Expr::apps(
        Expr::const_(Name::from_string("Eq.rec"), vec![one.clone(), one.clone()]),
        [
            nat.clone(),
            zero.clone(),
            motive,
            zero.clone(),
            zero.clone(),
            refl(one.clone(), nat.clone(), zero.clone()),
        ],
    );
    theorem(
        "recEq",
        eq(one.clone(), nat.clone(), rec_eq, zero.clone()),
        refl(one, nat, zero),
    )
}

fn lean_bytes(bytes: &[u8]) -> String {
    format!(
        "⟨#[{}]⟩",
        bytes
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

#[test]
fn automatic_candidates_replay_with_beta_zeta_and_local_definition_guards() {
    let env = Environment::default();
    let prop = Expr::sort(Level::zero());
    let id_type = pi(prop.clone(), pi(Expr::bvar(0), Expr::bvar(1)));
    let id_value = lam(prop.clone(), lam(Expr::bvar(0), Expr::bvar(0)));
    let beta_codomain = Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(1));
    let beta_type = pi(prop.clone(), pi(Expr::bvar(0), beta_codomain));
    let zeta_type = pi(
        prop.clone(),
        pi(
            Expr::bvar(0),
            let_expr(prop.clone(), Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let local_value = lam(
        prop.clone(),
        let_expr(
            prop.clone(),
            pi(Expr::bvar(0), Expr::bvar(1)),
            let_expr(
                Expr::bvar(0),
                lam(Expr::bvar(1), Expr::bvar(0)),
                Expr::bvar(0),
            ),
        ),
    );
    // The two functions differ, but both applications reduce to P. The
    // resulting declaration advice must replay despite their different bodies.
    let rollback_type = pi(
        prop.clone(),
        pi(
            Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(0)),
            Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(1)),
        ),
    );
    let rollback_value = lam(
        prop.clone(),
        lam(
            Expr::app(lam(prop.clone(), Expr::bvar(1)), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    );
    let cases = [
        definition("identityProp", id_type.clone(), id_value.clone()),
        definition("betaResult", beta_type, id_value.clone()),
        definition("zetaResult", zeta_type, id_value),
        definition("localFunction", id_type, local_value),
        definition("rollbackResult", rollback_type, rollback_value),
    ];
    let candidates = cases
        .iter()
        .map(|declaration| {
            produce_ordinary(&env, declaration, 100_000, 256)
                .expect("ordinary-core candidate search")
        })
        .collect::<Vec<_>>();
    // This checks an ordering obligation of the real beta cursor, not merely
    // round-tripping the writer with a native decoder of the same design.
    let zero_depths = candidates
        .iter()
        .map(|candidate| {
            let mut tokens = candidate.tokens.clone();
            match tokens.first_mut() {
                Some(Token::Depth(depth)) => *depth = 0,
                _ => panic!("producer must supply its declaration depth"),
            }
            lean_bytes(&encode_tokens(&tokens))
        })
        .collect::<Vec<_>>()
        .join(",");
    let beta = &candidates[1];
    let guard = beta
        .tokens
        .windows(2)
        .position(|pair| matches!(pair, [Token::CoreR(1), Token::Dom]))
        .expect("beta result conversion emits CORE_R before DOM");
    let mut omitted = beta.tokens.clone();
    omitted.remove(guard + 1);
    let mut reversed = beta.tokens.clone();
    reversed.swap(guard, guard + 1);
    let alias_name = Name::from_string("adviceAliasProp");
    let alias_type = Expr::sort(Level::succ(Level::zero()));
    let alias = definition("adviceAliasProp", alias_type.clone(), prop.clone());
    let alias_candidate =
        produce_ordinary(&env, &alias, 100_000, 256).expect("candidate for dependency prefix");
    let mut prefix = Environment::default();
    prefix.add_decl(alias).expect("native source prefix setup");
    let dependent = definition(
        "identityAlias",
        pi(
            Expr::const_(alias_name.clone(), vec![]),
            pi(Expr::bvar(0), Expr::bvar(1)),
        ),
        lam(prop.clone(), lam(Expr::bvar(0), Expr::bvar(0))),
    );
    let dependent_candidate = produce_ordinary(&prefix, &dependent, 100_000, 256)
        .expect("candidate with an explicit delta step");
    assert!(dependent_candidate
        .tokens
        .iter()
        .any(|token| matches!(token, Token::DeltaR)));
    let dependent_frames = encode_frames(&[alias_candidate.bytes, dependent_candidate.bytes]);
    let mut opaque_prefix = Environment::default();
    opaque_prefix
        .add_decl(Declaration::Opaque {
            name: alias_name,
            level_params: vec![],
            type_: alias_type,
            value: prop,
        })
        .expect("opaque prefix setup");
    assert!(
        produce_ordinary(&opaque_prefix, &dependent, 100_000, 256).is_err(),
        "producer must not unfold an opaque dependency"
    );
    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases

def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)
def pSort : X := srt .zero
def identityType : X := pis pSort (pis (.bvar 0) (.bvar 1))
def identityBody : X := lm pSort (lm (.bvar 0) (.bvar 0))
def betaType : X := pis pSort (pis (.bvar 0) (.app (lm pSort (.bvar 0)) (.bvar 1)))
def zetaType : X := pis pSort (pis (.bvar 0) (.letE `Q pSort (.bvar 1) (.bvar 0) false))
def localBody : X := lm pSort (.letE `T pSort (pis (.bvar 0) (.bvar 1))
  (.letE `f (.bvar 0) (lm (.bvar 1) (.bvar 0)) (.bvar 0) false) false)
def rollbackType : X := pis pSort (pis
  (.app (lm pSort (.bvar 0)) (.bvar 0))
  (.app (lm pSort (.bvar 0)) (.bvar 1)))
def rollbackBody : X := lm pSort (lm
  (.app (lm pSort (.bvar 1)) (.bvar 0)) (.bvar 0))
def accepted (input : DeclarationInput Unit) (bytes : ByteArray) : Bool :=
  match kcheckBytes base input bytes with | .ok _ => true | _ => false

def main : IO Unit := do
  expect "automatic-identity" (accepted (defn "identityProp" identityType identityBody) IDENTITY_BYTES)
  expect "automatic-beta" (accepted (defn "betaResult" betaType identityBody) BETA_BYTES)
  expect "automatic-zeta" (accepted (defn "zetaResult" zetaType identityBody) ZETA_BYTES)
  expect "automatic-local-definition" (accepted (defn "localFunction" identityType localBody) LOCAL_BYTES)
  expect "automatic-failed-branch-rollback" (accepted (defn "rollbackResult" rollbackType rollbackBody) ROLLBACK_BYTES)
  let ordinaryInputs := [defn "identityProp" identityType identityBody,
    defn "betaResult" betaType identityBody, defn "zetaResult" zetaType identityBody,
    defn "localFunction" identityType localBody, defn "rollbackResult" rollbackType rollbackBody]
  let zeroDepths : List ByteArray := [ZERO_DEPTH_BYTES]
  expect "every-ordinary-case-has-depth-refusal"
    (ordinaryInputs.length == 5 && zeroDepths.length == 5 &&
      (ordinaryInputs.zip zeroDepths).all (fun p =>
        match kcheckBytes base p.1 p.2 with | .error .depth => true | _ => false))
  let aliasInput := defn "adviceAliasProp" (srt (.succ .zero)) pSort
  let aliasIdentity := defn "identityAlias" (pis (.const (nm "adviceAliasProp") []) (pis (.bvar 0) (.bvar 1))) identityBody
  expect "automatic-delta-prefix" (match kcheckRun [aliasInput, aliasIdentity] DEPENDENT_FRAMES with
    | .ok (_, [_, _]) => true | _ => false)
  expect "opaque-delta-refused" (match kcheckRun [opq "adviceAliasProp" (srt (.succ .zero)) pSort, aliasIdentity] DEPENDENT_FRAMES with
    | .error (.deltaOpaque _) => true | _ => false)
  expect "missing-dom-refused-at-beta" (match kcheckBytes base (defn "betaResult" betaType identityBody) OMITTED_BYTES with
    | .error (.token .beta _) => true | _ => false)
  expect "reversed-dom-refused-at-conv" (match kcheckBytes base (defn "betaResult" betaType identityBody) REVERSED_BYTES with
    | .error (.token .conv .dom) => true | _ => false)
"#
    .replace("ZERO_DEPTH_BYTES", &zero_depths)
    .replace("ROLLBACK_BYTES", &lean_bytes(&candidates[4].bytes))
    .replace("DEPENDENT_FRAMES", &lean_bytes(&dependent_frames))
    .replace("IDENTITY_BYTES", &lean_bytes(&candidates[0].bytes))
    .replace("BETA_BYTES", &lean_bytes(&candidates[1].bytes))
    .replace("ZETA_BYTES", &lean_bytes(&candidates[2].bytes))
    .replace("LOCAL_BYTES", &lean_bytes(&candidates[3].bytes))
    .replace("OMITTED_BYTES", &lean_bytes(&encode_tokens(&omitted)))
    .replace("REVERSED_BYTES", &lean_bytes(&encode_tokens(&reversed)));
    let scratch = tempfile::tempdir().expect("private actual producer replay scratch");
    let file = scratch.path().join("AutomaticReplay.lean");
    std::fs::write(&file, source).expect("write actual native candidate input");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean executable");
    let output = Command::new(lean)
        .arg("--run")
        .arg(&file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean search path"),
        )
        .output()
        .expect("execute adopted checker on actual generated candidates");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout)
            .expect("UTF-8 replay")
            .lines()
            .collect::<Vec<_>>(),
        [
            "automatic-identity",
            "automatic-beta",
            "automatic-zeta",
            "automatic-local-definition",
            "automatic-failed-branch-rollback",
            "every-ordinary-case-has-depth-refusal",
            "automatic-delta-prefix",
            "opaque-delta-refused",
            "missing-dom-refused-at-beta",
            "reversed-dom-refused-at-conv",
        ]
    );
}

#[test]
fn automatic_iota_and_k_candidates_follow_the_adopted_cursor_and_replay_as_frames() {
    let (env, labelled) = nat_eq_fixture();
    let declarations = [
        rec_zero_declaration(),
        rec_succ_declaration(),
        rec_eq_declaration(),
        rec_k_declaration(),
    ];
    match produce_ordinary_with_labelled(
        &env,
        &LabelledEnvironment::default(),
        &declarations[0],
        1_000_000,
        32,
    ) {
        Err(Refusal::Coverage { source_name, .. }) => {
            assert_eq!(source_name, "advice_conversion_search_incomplete");
        }
        Err(other) => panic!("unexpected missing-labelled-prefix refusal: {other:?}"),
        Ok(_) => panic!("ordinary checking requires the admitted labelled prefix syntax"),
    }
    let prefix_names = ["Nat", "Nat.zero", "Nat.succ", "Eq", "Eq.refl"].map(Name::from_string);
    let mut prefix_tracer = CoreTracer::new(&env, 1_000_000);
    let mut labelled_without_rules = prefix_tracer
        .annotate_group(&prefix_names)
        .expect("labelled recursor-free prefix");
    let nat_rec = Name::from_string("Nat.rec");
    let nat_rec_info = env.get_const(&nat_rec).expect("native Nat.rec declaration");
    let (nat_rec_type, _) = prefix_tracer
        .check(&nat_rec_info.type_)
        .expect("labelled Nat.rec type without installing its rules");
    labelled_without_rules.insert(nat_rec, (nat_rec_type, None));
    match produce_ordinary_with_labelled(
        &env,
        &labelled_without_rules,
        &declarations[0],
        1_000_000,
        32,
    ) {
        Err(Refusal::Coverage { source_name, .. }) => {
            // Conversion search rolls back failed head-step alternatives and
            // exposes its final generic refusal, rather than the branch-local
            // missing-rule source. This prefix differs from the positive one
            // exactly by retaining the syntax entries without recursor rules.
            assert_eq!(source_name, "advice_conversion_search_incomplete");
        }
        Err(other) => panic!("unexpected missing-labelled-rule refusal: {other:?}"),
        Ok(_) => panic!("recursor advice requires the admitted labelled rule syntax"),
    }
    let candidates = declarations
        .iter()
        .map(|declaration| {
            let name = match declaration {
                Declaration::Definition { name, .. }
                | Declaration::Theorem { name, .. }
                | Declaration::Opaque { name, .. }
                | Declaration::Axiom { name, .. } => name,
            };
            produce_ordinary_with_labelled(&env, &labelled, declaration, 1_000_000, 32)
                .unwrap_or_else(|error| panic!("bounded recursor candidate {name}: {error:?}"))
        })
        .collect::<Vec<_>>();

    let iota = candidates[0]
        .tokens
        .iter()
        .position(|token| matches!(token, Token::Iota))
        .expect("Nat.zero conversion uses IOTA");
    assert_eq!(
        &candidates[0].tokens[iota..iota + 4],
        &[
            Token::Iota,
            Token::Stop,
            Token::SpineRefl(4),
            Token::SpineRefl(0),
        ],
        "IOTA precedes major WHNF and both telescope walks"
    );
    assert_eq!(
        candidates[0]
            .tokens
            .iter()
            .filter(|token| matches!(token, Token::Iota))
            .count(),
        1
    );
    assert!(!candidates[0]
        .tokens
        .iter()
        .any(|token| matches!(token, Token::K)));

    assert!(
        candidates[1].tokens.windows(4).any(|window| {
            window
                == [
                    Token::Iota,
                    Token::Stop,
                    Token::SpineRefl(4),
                    Token::SpineRefl(1),
                ]
        }),
        "Nat.succ IOTA walks its constructor field before applying the recursive RHS"
    );
    assert_eq!(
        candidates[1]
            .tokens
            .iter()
            .filter(|token| matches!(token, Token::Iota))
            .count(),
        2,
        "Nat.succ RHS recursively reduces the predecessor case"
    );

    let eq_iota = candidates[2]
        .tokens
        .iter()
        .position(|token| matches!(token, Token::Iota))
        .expect("Eq.refl major uses IOTA");
    assert_eq!(
        &candidates[2].tokens[eq_iota..eq_iota + 7],
        &[
            Token::Iota,
            Token::Stop,
            Token::SpineRefl(6),
            Token::SpineRefl(2),
            Token::Refl,
            Token::Refl,
            Token::Refl,
        ],
        "indexed IOTA ties both parameters and the fixed result index"
    );

    let k = candidates[3]
        .tokens
        .iter()
        .position(|token| matches!(token, Token::K))
        .expect("Eq.rec on a local proof uses K");
    assert_eq!(
        &candidates[3].tokens[k..k + 3],
        &[Token::K, Token::SpineRefl(6), Token::Refl],
        "K has one recursor walk and one index tie, without a major WHNF or constructor walk"
    );
    assert_eq!(
        candidates[3]
            .tokens
            .iter()
            .filter(|token| matches!(token, Token::K))
            .count(),
        1
    );
    assert!(!candidates[3]
        .tokens
        .iter()
        .any(|token| matches!(token, Token::Iota)));
    let frames = encode_frames(&[
        candidates[0].bytes.clone(),
        candidates[1].bytes.clone(),
        candidates[2].bytes.clone(),
        candidates[3].bytes.clone(),
    ]);
    let mut nat_as_k = candidates[0].tokens.clone();
    nat_as_k[iota] = Token::K;
    let mut k_as_iota = candidates[3].tokens.clone();
    k_as_iota[k] = Token::Iota;
    let mut nat_missing_major_stop = candidates[0].tokens.clone();
    assert_eq!(nat_missing_major_stop.remove(iota + 1), Token::Stop);
    let mut nat_missing_walk = candidates[0].tokens.clone();
    assert!(matches!(
        nat_missing_walk.remove(iota + 3),
        Token::SpineRefl(0)
    ));
    let mut nat_reordered_major_and_walk = candidates[0].tokens.clone();
    nat_reordered_major_and_walk.swap(iota + 1, iota + 2);
    let mut nat_shallow_depth = candidates[0].tokens.clone();
    let depth = nat_shallow_depth
        .iter()
        .position(|token| matches!(token, Token::Depth(_)))
        .expect("candidate carries its depth counter");
    assert!(matches!(nat_shallow_depth[depth], Token::Depth(n) if n > 0));
    nat_shallow_depth[depth] = Token::Depth(0);
    let mut eq_missing_result_tie = candidates[2].tokens.clone();
    assert_eq!(eq_missing_result_tie.remove(eq_iota + 6), Token::Refl);
    let mut k_extra_constructor_walk = candidates[3].tokens.clone();
    k_extra_constructor_walk.insert(k + 2, Token::SpineRefl(0));
    let mut k_missing_index_tie = candidates[3].tokens.clone();
    assert_eq!(k_missing_index_tie.remove(k + 2), Token::Refl);

    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases

def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)
def refused (input : DeclarationInput Unit) (bytes : ByteArray) : Bool :=
  match kcheckBytes base input bytes with | .error _ => true | _ => false
def nativeRecEqDecl : DeclarationInput Unit :=
  thm "recEq" (eqE (lvl 1) nat (eqRec (reflE (lvl 1) nat zero)) zero)
    (reflE (lvl 1) nat zero)
def nativeRecSuccDecl : DeclarationInput Unit :=
  thm "recSucc" (eqE (lvl 1) nat (natRec (succ zero)) (succ zero))
    (reflE (lvl 1) nat (succ zero))

def main : IO Unit := do
  expect "native-iota-k-framed-run" (match kcheckRun [recZeroDecl, nativeRecSuccDecl, nativeRecEqDecl, recKDecl] FRAMES with
    | .ok (_, [_, _, _, _]) => true | _ => false)
  expect "nat-iota-as-k-refused" (refused recZeroDecl NAT_AS_K)
  expect "eq-k-as-iota-refused" (refused recKDecl K_AS_IOTA)
  expect "iota-major-stop-required" (refused recZeroDecl NAT_MISSING_STOP)
  expect "iota-two-walk-certificates-required" (refused recZeroDecl NAT_MISSING_WALK)
  expect "iota-major-before-walk-required" (refused recZeroDecl NAT_REORDERED_MAJOR_WALK)
  expect "iota-depth-count-required" (refused recZeroDecl NAT_SHALLOW_DEPTH)
  expect "iota-result-tie-required" (refused nativeRecEqDecl EQ_MISSING_RESULT_TIE)
  expect "k-has-no-constructor-walk" (refused recKDecl K_EXTRA_CTOR_WALK)
  expect "k-index-tie-required" (refused recKDecl K_MISSING_INDEX_TIE)
"#
    .replace(
        "NAT_MISSING_WALK",
        &lean_bytes(&encode_tokens(&nat_missing_walk)),
    )
    .replace(
        "NAT_REORDERED_MAJOR_WALK",
        &lean_bytes(&encode_tokens(&nat_reordered_major_and_walk)),
    )
    .replace(
        "EQ_MISSING_RESULT_TIE",
        &lean_bytes(&encode_tokens(&eq_missing_result_tie)),
    )
    .replace(
        "K_MISSING_INDEX_TIE",
        &lean_bytes(&encode_tokens(&k_missing_index_tie)),
    )
    .replace(
        "K_EXTRA_CTOR_WALK",
        &lean_bytes(&encode_tokens(&k_extra_constructor_walk)),
    )
    .replace(
        "NAT_MISSING_STOP",
        &lean_bytes(&encode_tokens(&nat_missing_major_stop)),
    )
    .replace(
        "NAT_SHALLOW_DEPTH",
        &lean_bytes(&encode_tokens(&nat_shallow_depth)),
    )
    .replace("K_AS_IOTA", &lean_bytes(&encode_tokens(&k_as_iota)))
    .replace("NAT_AS_K", &lean_bytes(&encode_tokens(&nat_as_k)))
    .replace("FRAMES", &lean_bytes(&frames));
    let scratch = tempfile::tempdir().expect("private recursor replay scratch");
    let file = scratch.path().join("AutomaticRecursorReplay.lean");
    std::fs::write(&file, source).expect("write actual recursor candidates");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean executable");
    let output = Command::new(lean)
        .arg("--run")
        .arg(&file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean search path"),
        )
        .output()
        .expect("execute adopted checker on generated recursor candidates");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout)
            .expect("UTF-8 recursor replay")
            .lines()
            .collect::<Vec<_>>(),
        [
            "native-iota-k-framed-run",
            "nat-iota-as-k-refused",
            "eq-k-as-iota-refused",
            "iota-major-stop-required",
            "iota-two-walk-certificates-required",
            "iota-major-before-walk-required",
            "iota-depth-count-required",
            "iota-result-tie-required",
            "k-has-no-constructor-walk",
            "k-index-tie-required",
        ]
    );
}

#[test]
fn observing_reference_replay_carries_exact_iota_and_k_frames() {
    use clean_olean::recheck_closed::reference_base::{
        reference_base_core_tracing, AdviceCandidateObservation,
    };
    use clean_olean::ClosedRecheckOptions;
    use std::collections::{BTreeMap, BTreeSet};

    let (mut env, labelled) = pinned_nat_eq_fixture();
    let declarations = [rec_zero_declaration(), rec_k_declaration()];
    let names = ["recZero", "recK"];
    let direct = names
        .iter()
        .zip(&declarations)
        .map(|(name, declaration)| {
            (
                *name,
                produce_ordinary_with_labelled(&env, &labelled, declaration, 1_000_000, 1_000_000)
                    .expect("direct bounded recursor candidate")
                    .bytes,
            )
        })
        .collect::<BTreeMap<_, _>>();
    for declaration in &declarations {
        env.add_decl(declaration.clone())
            .expect("actual observing source declaration");
    }
    let targets = names
        .into_iter()
        .map(Name::from_string)
        .collect::<BTreeSet<_>>();
    let mut observed = Vec::new();
    let mut observed_names = BTreeSet::new();
    let report = reference_base_core_tracing(
        &env,
        &targets,
        &ClosedRecheckOptions::default(),
        1_000_000,
        None,
        &mut |row| {
            if names.contains(&row.name.as_str()) {
                let bytes = match row.advice_candidate.as_ref() {
                    Some(AdviceCandidateObservation::Candidate { bytes, .. }) => bytes.clone(),
                    other => panic!("observing caller did not produce {}: {other:?}", row.name),
                };
                assert!(
                    observed_names.insert(row.name.clone()),
                    "duplicate observing row {}",
                    row.name
                );
                observed.push((row.name.clone(), row.reference_accepted, bytes));
            }
        },
    )
    .expect("actual fenced observing replay");
    assert!(report.passed(), "{:#?}", report.refusals);
    assert_eq!(
        observed.len(),
        names.len(),
        "observing caller must emit exactly the two requested target frames"
    );
    let mut caller_frames = Vec::new();
    let mut caller_declarations = Vec::new();
    for (name, accepted, bytes) in &observed {
        let expected = direct
            .get(name.as_str())
            .unwrap_or_else(|| panic!("unexpected observing row {name}"));
        assert!(*accepted, "reference entry independently refused {name}");
        assert_eq!(
            bytes, expected,
            "caller and direct producer diverged for {name}"
        );
        caller_declarations.push(match name.as_str() {
            "recZero" => "recZeroDecl",
            "recK" => "recKDecl",
            _ => unreachable!("target names were checked above"),
        });
        caller_frames.push(bytes.clone());
    }

    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases
def main : IO Unit :=
  match kcheckRun CALLER_DECLARATIONS CALLER_FRAMES with
  | .ok (_, [_, _]) => IO.println "observing-iota-k-frames-replayed"
  | _ => throw (IO.userError "observing replay refused")
"#
    .replace(
        "CALLER_DECLARATIONS",
        &format!("[{}]", caller_declarations.join(", ")),
    )
    .replace("CALLER_FRAMES", &lean_bytes(&encode_frames(&caller_frames)));
    let scratch = tempfile::tempdir().expect("private observing recursor scratch");
    let file = scratch.path().join("ObservingRecursorReplay.lean");
    std::fs::write(&file, source).expect("write observing recursor replay");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let output = Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg("--run")
        .arg(file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .output()
        .expect("actual checker on observing recursor frames");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).expect("UTF-8 observing replay"),
        "observing-iota-k-frames-replayed\n"
    );
}

#[test]
fn incomplete_search_never_returns_a_partial_frame() {
    let env = Environment::default();
    let prop = Expr::sort(Level::zero());
    let invalid = definition("external", prop.clone(), Expr::fvar(FVarId::new(0)));
    assert!(
        matches!(produce_ordinary(&env, &invalid, 100, 256), Err(Refusal::Coverage { source_name, .. }) if source_name == "advice_non_core_input")
    );
    let empty_budget = definition("emptyBudget", prop.clone(), prop);
    assert!(matches!(
        produce_ordinary(&env, &empty_budget, 0, 256),
        Err(Refusal::Budget)
    ));
    let (env, labelled) = nat_eq_fixture();
    assert!(matches!(
        produce_ordinary_with_labelled(&env, &labelled, &rec_zero_declaration(), 1, 32),
        Err(Refusal::Budget)
    ));
}

#[test]
fn observing_reference_replay_emits_candidates_without_granting_admission() {
    use clean_olean::recheck_closed::reference_base::reference_base_core_tracing;
    use clean_olean::ClosedRecheckOptions;
    use std::collections::BTreeSet;

    let prop = Expr::sort(Level::zero());
    let declaration = definition(
        "callerIdentity",
        pi(prop.clone(), pi(Expr::bvar(0), Expr::bvar(1))),
        lam(prop, lam(Expr::bvar(0), Expr::bvar(0))),
    );
    let mut env = Environment::for_lean_replay();
    env.add_decl(declaration)
        .expect("ordinary input for actual caller");
    let targets = BTreeSet::from([Name::from_string("callerIdentity")]);
    let observe = |operations| {
        let mut rows = Vec::new();
        let report = reference_base_core_tracing(
            &env,
            &targets,
            &ClosedRecheckOptions::default(),
            operations,
            None,
            &mut |row| rows.push(serde_json::to_value(row).expect("serialize actual observation")),
        )
        .expect("actual fenced observing replay");
        assert!(
            report.passed(),
            "candidate search cannot replace the reference verdict"
        );
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["reference_accepted"], true);
        rows.remove(0)
    };
    let exhausted = observe(0);
    assert_eq!(exhausted["advice_candidate"]["status"], "refused");
    assert!(exhausted["advice_candidate"].get("bytes").is_none());
    let candidate = observe(100_000);
    assert_eq!(candidate["advice_candidate"]["status"], "candidate");
    assert_eq!(candidate["advice_candidate"]["depth"], 100_000);
    let bytes = candidate["advice_candidate"]["bytes"]
        .as_array()
        .expect("actual caller exports candidate bytes")
        .iter()
        .map(|byte| u8::try_from(byte.as_u64().expect("byte integer")).expect("byte range"))
        .collect::<Vec<_>>();
    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases
def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)
def callerInput : DeclarationInput Unit := defn "callerIdentity"
  (pis (srt .zero) (pis (.bvar 0) (.bvar 1)))
  (lm (srt .zero) (lm (.bvar 0) (.bvar 0)))
def candidate : ByteArray := CANDIDATE_BYTES
def main : IO Unit := do
  expect "caller-candidate-replayed" (match kcheckBytes base callerInput candidate with
    | .ok _ => true | _ => false)
  expect "caller-trailing-token-refused" (match kcheckBytes base callerInput (candidate.push 0) with
    | .error _ => true | _ => false)
"#
    .replace("CANDIDATE_BYTES", &lean_bytes(&bytes));
    let scratch = tempfile::tempdir().expect("actual caller replay scratch");
    let file = scratch.path().join("CallerReplay.lean");
    std::fs::write(&file, source).expect("write original caller input");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let output = Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg("--run")
        .arg(file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .output()
        .expect("actual checker on observing-caller bytes");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).expect("UTF-8 replay"),
        "caller-candidate-replayed\ncaller-trailing-token-refused\n"
    );
}
