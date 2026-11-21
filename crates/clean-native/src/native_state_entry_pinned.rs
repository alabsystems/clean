// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct 4.30 SDK actions that return an original success or literal user error
//! with their input world token.

use super::*;
use clean_compiler::lcnf::{Arg, Code, DeclValue, LetValue};
use clean_kernel::{ConstantKind, Level};

#[derive(Clone, Copy)]
pub(super) enum DirectResult<'a> {
    Success,
    UserError(&'a str),
}

impl StateEntry {
    pub(in crate::native_build) fn is_pinned_direct_action(env: &Environment, root: &Name) -> bool {
        direct_result(env, root).is_some()
    }
}

pub(super) fn direct_result<'a>(env: &'a Environment, root: &Name) -> Option<DirectResult<'a>> {
    if clean_olean::environment_world(env) != Some(LeanWorld::Lean430Rc2.tag()) {
        return None;
    }
    let info = env.get_const(root)?;
    let ExprKind::App(io, entry_result) = info.type_.kind() else {
        return None;
    };
    if io.as_ref() != &Expr::const_str("IO") {
        return None;
    }
    let ExprKind::Lam(_, binder, body) = info.value.as_ref()?.strip_mdata().kind() else {
        return None;
    };
    let body = body.strip_mdata();
    let args = body.get_app_args();
    let [error, world, result, payload, state] = args.as_slice() else {
        return None;
    };
    // Bootstrap keeps its eager ABI. If either side comes from the SDK,
    // StateEntry::check verifies both owners before decoding the result.
    if !imported(env, "IO", "Init.System.IO") && !imported(env, "EST.Out", "Init.System.ST") {
        return None;
    }
    let status = entry_result.as_ref() == &Expr::const_str("UInt32");
    if !status && entry_result.as_ref() != &Expr::const_str("Unit") {
        return None;
    }
    let constructor = body.get_app_fn();
    let direct = if constructor == &Expr::const_str("EST.Out.ok") {
        if (status && payload.has_loose_bvars())
            || (!status && payload.strip_mdata() != &Expr::const_str("Unit.unit"))
        {
            return None;
        }
        DirectResult::Success
    } else if constructor == &Expr::const_str("EST.Out.error") {
        let ExprKind::App(user, message) = payload.strip_mdata().kind() else {
            return None;
        };
        if user.as_ref() != &Expr::const_str("IO.Error.userError") {
            return None;
        }
        let ExprKind::Lit(clean_kernel::Literal::String(text)) = message.strip_mdata().kind()
        else {
            return None;
        };
        DirectResult::UserError(text)
    } else {
        return None;
    };
    let real_world = Expr::const_str("IO.RealWorld");
    let tc = TypeChecker::new(env);
    (state.strip_mdata() == &Expr::bvar(0)
        && tc.is_def_eq(
            binder,
            &Expr::app(Expr::const_str("Void"), real_world.clone()),
        )
        && tc.is_def_eq(error, &Expr::const_str("IO.Error"))
        && tc.is_def_eq(world, &real_world)
        && tc.is_def_eq(result, entry_result))
    .then_some(direct)
}

/// The native Unit.unit shim returns the tag of the sole nullary PUnit constructor.
fn check_unit_literal(env: &Environment, root: &Name) -> anyhow::Result<()> {
    let unit = Name::interned("Unit");
    let literal = Name::interned("Unit.unit");
    let punit = Name::interned("PUnit");
    let ctor = Name::interned("PUnit.unit");
    anyhow::ensure!(
        ["Unit", "Unit.unit", "PUnit", "PUnit.unit"]
            .into_iter()
            .all(|name| imported(env, name, "Init.Prelude"))
            && clean_compiler::resolve_csimp_reference(env, Some(root), &literal)? == literal
            && clean_compiler::resolve_csimp_reference(env, Some(&literal), &ctor)? == ctor,
        "invalid pinned Unit literal owner or compiler binding"
    );
    let original_alias = |name: &Name, ty: Expr, target: &Name| {
        env.get_const(name).is_some_and(|info| {
            info.kind == ConstantKind::Definition
                && info.level_params.is_empty()
                && info.type_ == ty
                && info.value.as_ref()
                    == Some(&Expr::const_(
                        target.clone(),
                        vec![Level::succ(Level::zero())],
                    ))
        })
    };
    anyhow::ensure!(
        original_alias(&unit, Expr::type_(), &punit)
            && original_alias(&literal, Expr::const_str("Unit"), &ctor),
        "invalid pinned Unit or Unit.unit abbreviation"
    );
    let family = env
        .get_inductive(&punit)
        .ok_or_else(|| anyhow!("missing PUnit family"))?;
    let constructor = env
        .get_constructor(&ctor)
        .ok_or_else(|| anyhow!("missing PUnit.unit constructor"))?;
    let [u] = family.level_params.as_slice() else {
        bail!("invalid PUnit universe parameters")
    };
    let level = Level::param(u.clone());
    anyhow::ensure!(
        family.num_params == 0
            && family.num_indices == 0
            && family.type_ == Expr::sort(level.clone())
            && family.constructor_names.as_slice() == std::slice::from_ref(&ctor)
            && constructor.inductive_name == punit
            && constructor.level_params == family.level_params
            && constructor.num_params == 0
            && constructor.num_fields == 0
            && constructor.constructor_idx == 0
            && constructor.type_ == Expr::const_(punit, vec![level]),
        "invalid pinned Unit literal constructor layout"
    );
    Ok(())
}

/// The boxed driver may decode only a result constructed by this actual root.
/// A compiled replacement, a raw scalar, or a returned action has a different ABI.
pub(super) fn check_lowered_result(
    env: &Environment,
    root: &Name,
    decl: &Decl,
    returns_status: bool,
    direct: DirectResult<'_>,
) -> anyhow::Result<()> {
    let constructor = match direct {
        DirectResult::Success => Name::interned("EST.Out.ok"),
        DirectResult::UserError(_) => Name::interned("EST.Out.error"),
    };
    anyhow::ensure!(
        clean_compiler::resolve_csimp_reference(env, Some(root), &constructor)? == constructor
            && (!returns_status || imported(env, "UInt32", "Init.Prelude"))
            && imported(env, "IO.Error", "Init.System.IOError")
            && !env.is_extern(root)
            && !env.has_implemented_by(root)
            && !env.is_unsafe(root)
            && !env.is_partial(root)
            && !env.is_noncomputable(root),
        "invalid pinned direct IO entry or result type"
    );
    let [world] = decl.params.as_slice() else {
        bail!("the pinned direct action lost its world parameter")
    };
    let DeclValue::Code(code) = &decl.body else {
        bail!("the pinned direct action lost its source body")
    };
    if let DirectResult::UserError(message) = direct {
        anyhow::ensure!(
            (returns_status || imported(env, "Unit", "Init.Prelude"))
                && imported(env, "String", "Init.Prelude")
                && clean_compiler::resolve_csimp_reference(
                    env,
                    Some(root),
                    &Name::interned("IO.Error.userError")
                )? == Name::interned("IO.Error.userError"),
            "invalid pinned user error owner or compiler binding"
        );
        return check_lowered_user_error(env, code, world.fvar_id, message, returns_status);
    }
    let mut code = code.as_ref();
    let unit_payload = if returns_status {
        None
    } else {
        check_unit_literal(env, root)?;
        let Code::Let(binding, next) = code else {
            bail!("missing lowered Unit.unit literal")
        };
        anyhow::ensure!(
            binding.ty == Expr::const_str("Unit")
                && matches!(&binding.value, LetValue::Const {name, levels, args}
                if name == &Name::interned("Unit.unit") && levels.is_empty() && args.is_empty()),
            "invalid lowered Unit.unit literal"
        );
        code = next;
        Some(Arg::FVar(binding.fvar_id))
    };
    while let Code::Let(binding, next) = code {
        if let Code::Return(id) = next.as_ref() {
            if *id == binding.fvar_id
                && matches!(&binding.value, LetValue::Const { name, args, .. } | LetValue::Ctor { name, args, .. }
                    if *name == constructor && args.last() == Some(&Arg::FVar(world.fvar_id))
                        && unit_payload.as_ref().is_none_or(|unit| matches!(args.as_slice(),
                            [Arg::Type(_), Arg::Type(_), Arg::Type(_), payload, _] if payload == unit)))
            {
                return Ok(());
            }
        }
        if unit_payload.is_some() {
            break;
        }
        code = next;
    }
    bail!("the pinned direct action does not return its selected EST.Out.ok constructor and world")
}

/// Require the original literal, applied userError constructor and returned error
/// with this exact input token. No other call or value can supply the payload.
fn check_lowered_user_error(
    env: &Environment,
    code: &Code,
    world: clean_kernel::FVarId,
    text: &str,
    returns_status: bool,
) -> anyhow::Result<()> {
    let Code::Let(message, next) = code else {
        bail!("missing lowered user error message")
    };
    let Code::Let(error, next) = next.as_ref() else {
        bail!("missing lowered user error constructor")
    };
    let Code::Let(result, next) = next.as_ref() else {
        bail!("missing lowered error result")
    };
    fn fields<'a>(value: &'a LetValue, expected: &str) -> Option<&'a [Arg]> {
        match value {
            LetValue::Const { name, levels, args } | LetValue::Ctor { name, levels, args }
                if name == &Name::interned(expected) && levels.is_empty() =>
            {
                Some(args)
            }
            _ => None,
        }
    }
    let Some(
        [Arg::Type(error_ty), Arg::Type(world_ty), Arg::Type(value_ty), Arg::FVar(payload), Arg::FVar(token)],
    ) = fields(&result.value, "EST.Out.error")
    else {
        bail!("invalid lowered error constructor fields")
    };
    // Lowering may already have unfolded the erased world or Unit aliases.
    // The two executable fields must use the actual local bindings verbatim.
    let tc = TypeChecker::new(env);
    let expected_result = Expr::apps(
        Expr::const_str("EST.Out"),
        [
            Expr::const_str("IO.Error"),
            Expr::const_str("IO.RealWorld"),
            Expr::const_str(if returns_status { "UInt32" } else { "Unit" }),
        ],
    );
    let mut ids = [world, message.fvar_id, error.fvar_id, result.fvar_id];
    ids.sort_unstable();
    anyhow::ensure!(
        ids.windows(2).all(|pair| pair[0] != pair[1])
            && message.ty == Expr::const_str("String")
            && matches!(&message.value, LetValue::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == text)
            && error.ty == Expr::const_str("IO.Error")
            && fields(&error.value, "IO.Error.userError")
                == Some([Arg::FVar(message.fvar_id)].as_slice())
            && tc.is_def_eq(&result.ty, &expected_result)
            && tc.is_def_eq(error_ty, &error.ty)
            && tc.is_def_eq(world_ty, &Expr::const_str("IO.RealWorld"))
            && tc.is_def_eq(
                value_ty,
                &Expr::const_str(if returns_status { "UInt32" } else { "Unit" })
            )
            && *payload == error.fvar_id
            && *token == world
            && matches!(next.as_ref(), Code::Return(id) if *id == result.fvar_id),
        "the pinned direct error must return the selected literal userError and original world"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ConstantOrigin;

    #[test]
    fn pinned_user_error_requires_the_same_literal_constructors_and_world_in_lowering() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Errors.lean");
        std::fs::write(
            &file,
            r#"prelude
import Init.System.IO
def statusError : IO UInt32 := fun s => EST.Out.error (IO.Error.userError "first") s
def unitError : IO Unit := fun s => EST.Out.error (IO.Error.userError "second") s
def namedMessage : String := "named"
def indirect : IO Unit := fun s => EST.Out.error (IO.Error.userError namedMessage) s
def otherError : IO Unit := fun s => EST.Out.error (IO.Error.otherError 37 "outside") s
def forwardWorld (s : Void IO.RealWorld) := s
def changedWorld : IO Unit := fun s => EST.Out.error (IO.Error.userError "first") (forwardWorld s)
@[noinline] def otherUser (s : String) := IO.Error.userError s
@[csimp] theorem replaceUser : Eq IO.Error.userError otherUser := Eq.refl IO.Error.userError
def afterRule : IO Unit := fun s => EST.Out.error (IO.Error.userError "second") s
"#,
        )
        .unwrap();
        let env = crate::compile::elaborate_file_to_env(&file).unwrap();
        for name in ["indirect", "otherError", "changedWorld"] {
            assert!(
                !StateEntry::is_pinned_direct_action(&env, &Name::interned(name)),
                "{name}"
            );
        }
        for (name, status) in [
            ("statusError", true),
            ("unitError", false),
            ("afterRule", false),
        ] {
            let root = Name::interned(name);
            let direct = direct_result(&env, &root).expect("direct literal error");
            let closure = clean_compiler::RuntimeBindingClosure::check_executable(
                &env,
                std::slice::from_ref(&root),
            )
            .unwrap();
            let decl = clean_compiler::constant_to_decl_in_runtime_closure(
                &env,
                env.get_const(&root).unwrap(),
                &closure,
            )
            .unwrap()
            .unwrap();
            let check = |env: &Environment, decl: &Decl| {
                check_lowered_result(env, &root, decl, status, direct)
            };
            if name == "afterRule" {
                assert!(
                    check(&env, &decl).is_err(),
                    "the new caller sees the substitute"
                );
                continue;
            }
            check(&env, &decl).unwrap_or_else(|e| panic!("{e:#}: {decl:?}"));
            for mutation in [
                "text",
                "user",
                "world",
                "world type",
                "constructor",
                "result",
                "result type",
                "reused binder",
            ] {
                let mut bad = decl.clone();
                let DeclValue::Code(body) = &mut bad.body else {
                    unreachable!()
                };
                let Code::Let(message, next) = body.as_mut() else {
                    unreachable!()
                };
                let Code::Let(error, next) = next.as_mut() else {
                    unreachable!()
                };
                let Code::Let(result, tail) = next.as_mut() else {
                    unreachable!()
                };
                match mutation {
                    "text" => {
                        message.value = LetValue::Lit(clean_kernel::Literal::String("other".into()))
                    }
                    "user" => error.value = LetValue::Erased,
                    "result" => **tail = Code::Return(error.fvar_id),
                    "result type" => result.ty = Expr::const_str("String"),
                    "reused binder" => {
                        result.fvar_id = bad.params[0].fvar_id;
                        **tail = Code::Return(result.fvar_id);
                    }
                    "world" | "world type" | "constructor" => {
                        let (ctor, args) = match &mut result.value {
                            LetValue::Const { name, args, .. }
                            | LetValue::Ctor { name, args, .. } => (name, args),
                            _ => unreachable!(),
                        };
                        if mutation == "world" {
                            *args.last_mut().unwrap() = Arg::FVar(message.fvar_id);
                        } else if mutation == "world type" {
                            args[1] = Arg::Type(Expr::const_str("String"));
                        } else {
                            *ctor = Name::interned("EST.Out.ok");
                        }
                    }
                    _ => unreachable!(),
                }
                assert!(check(&env, &bad).is_err(), "{name}: {mutation}");
            }
            let mut wrong_owner = env.clone();
            assert!(wrong_owner.set_constant_origin(
                Name::interned("String"),
                ConstantOrigin::clean_payload(Some("Init.Prelude".to_owned()))
            ));
            assert!(check(&wrong_owner, &decl).is_err());
        }
    }

    #[test]
    fn original_direct_status_checks_the_selected_result_and_world() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Entry.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init.System.IO\n\n\
            @[noinline] def observedStatus : UInt32 := 23\n\
            def literalStatus : IO UInt32 := fun s => EST.Out.ok 7 s\n\
            def liveStatus : IO UInt32 := fun s => EST.Out.ok observedStatus s\n\
            @[noinline] def useToken (_s : Void IO.RealWorld) : UInt32 := 7\n\
            def tokenStatus : IO UInt32 := fun s => EST.Out.ok (useToken s) s\n\
            def otherStatus : IO UInt32 := pure 7\n",
        )
        .unwrap();
        let env = crate::compile::elaborate_file_to_env(&file).unwrap();
        for name in ["tokenStatus", "otherStatus"] {
            assert!(!StateEntry::is_pinned_direct_action(
                &env,
                &Name::interned(name)
            ));
        }
        for name in ["liveStatus", "literalStatus"] {
            let root = Name::interned(name);
            let info = env.get_const(&root).unwrap();
            assert!(
                StateEntry::is_pinned_direct_action(&env, &root),
                "{name}: {:?}",
                info.value
            );
            let closure = clean_compiler::RuntimeBindingClosure::check_executable(
                &env,
                std::slice::from_ref(&root),
            )
            .unwrap();
            let mut decl =
                clean_compiler::constant_to_decl_in_runtime_closure(&env, info, &closure)
                    .unwrap()
                    .unwrap();
            let check = |env: &Environment, decl: &Decl| {
                StateEntry::check(env, &root, std::slice::from_ref(decl))
            };
            let checked = check(&env, &decl)
                .unwrap_or_else(|e| panic!("{e:#}: {decl:?}"))
                .expect("original pinned state entry");
            assert!(checked.action_body);
            assert_eq!(checked.user_error, None);
            assert_eq!(
                checked.erased_world_fields,
                clean_compiler::world_token::has_checked_void_layout(&env)
            );
            let actual = if checked.physical_world_parameter {
                "clean_obj* _x0"
            } else {
                "void"
            };
            checked
                .contract(&format!("clean_obj* l_entry({actual}) {{"), "l_entry")
                .unwrap();
            assert!(checked
                .contract("uint32_t l_entry(void) {", "l_entry")
                .is_err());
            for name in ["IO", "EST.Out.ok", "IO.RealWorld", "UInt32"] {
                let mut substituted = env.clone();
                assert!(substituted.set_constant_origin(
                    Name::interned(name),
                    ConstantOrigin::clean_payload(Some("Other.Module".to_owned()))
                ));
                assert!(check(&substituted, &decl).is_err(), "{name}");
            }
            let mut alternative = env.clone();
            alternative.register_extern(root.clone(), "different_status_result".to_owned());
            assert!(check(&alternative, &decl).is_err());
            decl.body = DeclValue::Code(Box::new(Code::Return(decl.params[0].fvar_id)));
            assert!(check(&env, &decl).is_err());
        }
    }

    #[test]
    fn pinned_unit_literal_requires_original_aliases_and_the_returned_object() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Entry.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init.System.IO\n\n\
            @[noinline] def namedUnit : Unit := @PUnit.unit.{1}\n\
            def otherPUnit.{u} : PUnit.{u} := PUnit.unit\n\
            @[csimp] theorem laterPUnit.{u} : @PUnit.unit.{u} = @otherPUnit.{u} := rfl\n\
            def literal : IO Unit := fun s => EST.Out.ok () s\n\
            def named : IO Unit := fun s => EST.Out.ok namedUnit s\n\
            @[csimp] theorem laterAlias : Unit.unit = namedUnit := rfl\n\
            def substituted : IO Unit := fun s => EST.Out.ok () s\n",
        )
        .unwrap();
        let env = crate::compile::elaborate_file_to_env(&file).unwrap();
        let root = Name::interned("literal");
        let alias = Name::interned("Unit.unit");
        let ctor = Name::interned("PUnit.unit");
        assert_ne!(
            clean_compiler::resolve_csimp_reference(&env, Some(&root), &ctor).unwrap(),
            ctor
        );
        assert_eq!(
            clean_compiler::resolve_csimp_reference(&env, Some(&alias), &ctor).unwrap(),
            ctor
        );
        assert!(!StateEntry::is_pinned_direct_action(
            &env,
            &Name::interned("named")
        ));
        let lower = |root: &Name| {
            let closure = clean_compiler::RuntimeBindingClosure::check_executable(
                &env,
                std::slice::from_ref(root),
            )
            .unwrap();
            clean_compiler::constant_to_decl_in_runtime_closure(
                &env,
                env.get_const(root).unwrap(),
                &closure,
            )
            .unwrap()
            .unwrap()
        };
        let decl = lower(&root);
        let check = |env: &Environment, root: &Name, decl: &Decl| {
            StateEntry::check(env, root, std::slice::from_ref(decl))
        };
        let checked = check(&env, &root, &decl)
            .unwrap()
            .expect("original literal compiled after a later constructor rule");
        assert_eq!(checked.contract.exit, EntryExit::AlwaysZero);
        assert!(checked.action_body && checked.user_error.is_none());
        let redirected = Name::interned("substituted");
        assert!(StateEntry::is_pinned_direct_action(&env, &redirected));
        assert_eq!(
            clean_compiler::resolve_csimp_reference(&env, Some(&redirected), &alias).unwrap(),
            Name::interned("namedUnit")
        );
        assert!(check(&env, &redirected, &lower(&redirected)).is_err());

        for name in ["Unit", "Unit.unit", "PUnit", "PUnit.unit"] {
            let mut foreign = env.clone();
            assert!(foreign.set_constant_origin(
                Name::interned(name),
                ConstantOrigin::clean_payload(Some("Init.Prelude".into()))
            ));
            assert!(check(&foreign, &root, &decl).is_err(), "{name}");
        }
        for name in [&alias, &ctor] {
            let mut binding = env.clone();
            binding.register_extern(name.clone(), "new_unit".into());
            assert!(check(&binding, &root, &decl).is_err(), "{name}");
            let mut replaced = env.clone();
            replaced.register_implemented_by(name.clone(), Name::interned("namedUnit"));
            assert!(check(&replaced, &root, &decl).is_err(), "{name}");
        }
        let mut changed = env.clone();
        let origin = changed.get_constant_origin(&alias).unwrap().clone();
        changed.forget_decl(&alias);
        changed
            .add_decl(clean_kernel::Declaration::Definition {
                name: alias.clone(),
                level_params: vec![],
                type_: Expr::const_str("Unit"),
                value: Expr::const_str("namedUnit"),
                is_reducible: true,
            })
            .unwrap();
        assert_eq!(changed.get_constant_origin(&alias), Some(&origin));
        assert!(imported(&changed, "Unit.unit", "Init.Prelude"));
        assert!(check(&changed, &root, &decl).is_err());

        let mut wrong = decl.clone();
        let DeclValue::Code(code) = &mut wrong.body else {
            panic!("expected selected action")
        };
        let Code::Let(unit, rest) = code.as_mut() else {
            panic!("expected literal binding")
        };
        let Code::Let(result, _) = rest.as_mut() else {
            panic!("expected result binding")
        };
        let LetValue::Const { args, .. } = &mut result.value else {
            panic!("expected result constructor")
        };
        assert_eq!(args[3], Arg::FVar(unit.fvar_id));
        args[3] = Arg::FVar(wrong.params[0].fvar_id);
        assert!(check(&env, &root, &wrong).is_err());
        let mut erased = decl.clone();
        let DeclValue::Code(code) = &mut erased.body else {
            unreachable!()
        };
        let Code::Let(unit, _) = code.as_mut() else {
            unreachable!()
        };
        unit.value = LetValue::Erased;
        assert!(check(&env, &root, &erased).is_err());
    }
}
