// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Native eta/irrelevance candidates replayed by the adopted checker, not authority.
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderData, Expr, ExprKind, FVarId};
use clean_kernel::kcheck_trace::core::advice::produce_ordinary;
use clean_kernel::kcheck_trace::wire::encode_tokens;
use clean_kernel::kcheck_trace::Token;
use clean_kernel::{Level, Name};
use clean_olean::test_support::compiled_fixture_dir;
use std::process::Command;

fn variable(index: u64) -> Expr {
    Expr::fvar(FVarId::new(index))
}
fn arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::pi(BinderData::default(), domain, codomain)
}
fn bind(binders: &[(u64, Expr)], mut body: Expr, lambda: bool) -> Expr {
    for (index, domain) in binders.iter().rev() {
        body = body.abstract_fvar(FVarId::new(*index));
        body = if lambda {
            Expr::lam(BinderData::default(), domain.clone(), body)
        } else {
            Expr::pi(BinderData::default(), domain.clone(), body)
        };
    }
    body
}
fn definition(name: &str, ty: Expr, body: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value: body,
        is_reducible: true,
    }
}
fn eta_declaration(right: bool) -> Declaration {
    let p = variable(0);
    let function_type = arrow(p.clone(), p.clone());
    let expansion = bind(&[(4, p.clone())], Expr::app(variable(1), variable(4)), true);
    let (source, target) = if right {
        (expansion, variable(1))
    } else {
        (variable(1), expansion)
    };
    let binders = [
        (0, Expr::sort(Level::zero())),
        (1, function_type.clone()),
        (2, arrow(function_type, Expr::sort(Level::zero()))),
        (3, Expr::app(variable(2), source)),
    ];
    definition(
        if right { "etaRight" } else { "etaLeft" },
        bind(&binders, Expr::app(variable(2), target), false),
        bind(&binders, variable(3), true),
    )
}
fn proof_declaration(proposition: bool) -> Declaration {
    let universe = if proposition {
        Level::zero()
    } else {
        Level::succ(Level::zero())
    };
    let p = variable(0);
    let binders = [
        (0, Expr::sort(universe)),
        (1, p.clone()),
        (2, p.clone()),
        (3, arrow(p, Expr::sort(Level::zero()))),
        (4, Expr::app(variable(3), variable(1))),
    ];
    definition(
        if proposition {
            "proofIndex"
        } else {
            "dataIndex"
        },
        bind(&binders, Expr::app(variable(3), variable(2)), false),
        bind(&binders, variable(4), true),
    )
}
// Independent raw-input spelling: no native annotations or inferred types are
// supplied to Lean. The actual checker reconstructs those from this original input.
fn lean_expr(expr: &Expr) -> String {
    match expr.kind() {
        ExprKind::BVar(index) => format!("(.bvar {index})"),
        ExprKind::Sort(level) => {
            let spelling = if *level == Level::zero() {
                ".zero"
            } else {
                assert_eq!(*level, Level::succ(Level::zero()));
                "(.succ .zero)"
            };
            format!("(srt {spelling})")
        }
        ExprKind::App(f, a) => format!("(ap {} {})", lean_expr(f), lean_expr(a)),
        ExprKind::Lam(_, a, b) => format!("(lm {} {})", lean_expr(a), lean_expr(b)),
        ExprKind::Pi(_, a, b) => format!("(pis {} {})", lean_expr(a), lean_expr(b)),
        other => panic!("unexpected raw extensional fixture input: {other:?}"),
    }
}
fn lean_decl(declaration: &Declaration) -> String {
    let Declaration::Definition {
        name, type_, value, ..
    } = declaration
    else {
        panic!("ordinary fixture")
    };
    format!(
        "(defn \"{name}\" {} {})",
        lean_expr(type_),
        lean_expr(value)
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
fn eta_both_directions_and_proof_irrelevance_replay_with_typed_refusals() {
    let env = Environment::default();
    let cases = [
        eta_declaration(false),
        eta_declaration(true),
        proof_declaration(true),
    ];
    let mut source = String::from("import KCheck.CheckerCases\nopen CICL KCheck KCheck.CheckerCases\ndef expect (label : String) (ok : Bool) : IO Unit :=\n  if ok then IO.println label else throw (IO.userError label)\ndef main : IO Unit := do\n");
    let mut proof_bytes = Vec::new();
    for (index, declaration) in cases.iter().enumerate() {
        let candidate =
            produce_ordinary(&env, declaration, 100_000, 512).expect("extensional candidate");
        let tag = match index {
            0 => Token::EtaL,
            1 => Token::EtaR,
            _ => Token::Irrel,
        };
        let site = candidate
            .tokens
            .iter()
            .position(|token| *token == tag)
            .expect("actual extensional search rule");
        let mut forged = candidate.tokens.clone();
        forged[site] = Token::Refl;
        let input = lean_decl(declaration);
        source.push_str(&format!("  expect \"extensional-{index}-accepted\" (match kcheckBytes base {input} {} with | .ok _ => true | _ => false)\n", lean_bytes(&candidate.bytes)));
        source.push_str(&format!("  expect \"extensional-{index}-forged-refl-refused\" (match kcheckBytes base {input} {} with | .error .refl => true | _ => false)\n", lean_bytes(&encode_tokens(&forged))));
        if index == 2 {
            proof_bytes = candidate.bytes;
        }
    }
    let data = proof_declaration(false);
    assert!(
        produce_ordinary(&env, &data, 100_000, 512).is_err(),
        "distinct data indices cannot be identified by proof irrelevance"
    );
    source.push_str(&format!("  expect \"irrelevance-non-prop-refused\" (match kcheckBytes base {} {} with | .error .notProp => true | _ => false)\n", lean_decl(&data), lean_bytes(&proof_bytes)));
    let scratch = tempfile::tempdir().expect("extensional actual replay scratch");
    let path = scratch.path().join("ExtensionalReplay.lean");
    std::fs::write(&path, source).expect("original native declarations and bytes");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned library");
    let output = Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg("--run")
        .arg(path)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .output()
        .expect("actual adopted checker extensional replay");
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
            "extensional-0-accepted",
            "extensional-0-forged-refl-refused",
            "extensional-1-accepted",
            "extensional-1-forged-refl-refused",
            "extensional-2-accepted",
            "extensional-2-forged-refl-refused",
            "irrelevance-non-prop-refused"
        ]
    );
}
