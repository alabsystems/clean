use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name, TypeChecker};
use clean_verify::source_ir_word64_addition as connection;
use std::sync::OnceLock;

mod retained_reader;
use retained_reader::read_retained_expr;
use trust_ir::{
    BlockId, CallingConv, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
    ValueId,
};
use trust_ir_build::{
    core_execution::{
        Assembler, Catalog, Coordinate, EntryTarget, Limits, MachineModel, NatTerm,
        PendingEquality, RootReturnFrame,
    },
    scoped_local::LocalScope,
    source_addition_data::RustU64AdditionModule,
    ModuleBuilder,
};
fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), x)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(t: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    let x: Vec<_> = x.into_iter().collect();
    x.into_iter()
        .rev()
        .fold(a("IRList.nil", [c(t)]), |tail, head| {
            a("IRList.cons", [c(t), head, tail])
        })
}
fn eq(t: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [t, l, r],
    )
}
fn refl(t: Expr, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [t, v],
    )
}
fn limits() -> Limits {
    Limits {
        max_operations: 4000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn environment() -> &'static Environment {
    static E: OnceLock<Environment> = OnceLock::new();
    E.get_or_init(|| connection::environment().unwrap())
}
fn module_fn(literal: u64) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "source_identity",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::Unclassified,
        },
    );
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let fid = builder.declare_function("identity", signature);
    {
        let mut f = builder.define_function(fid).unwrap();
        f.set_calling_conv(CallingConv::Rust);
        let bb = f.create_block();
        let p = f.add_block_param(bb, Ty::U64);
        f.switch_to_block(bb);
        let k = f.iconst(Ty::U64, i128::from(literal));
        let sum = f.add(Ty::U64, p, k);
        f.ret(vec![sum]);
        f.build();
    }
    let mut module = builder.build().unwrap();
    let f = &mut module.functions[0];
    f.id = FuncId(41);
    f.entry = BlockId(17);
    f.blocks[0].id = BlockId(17);
    f.blocks[0].params[0].0 = ValueId(31);
    f.blocks[0].body[0].results = vec![ValueId(57)];
    f.blocks[0].body[1].results = vec![ValueId(81)];
    f.blocks[0].body[1].inst = Inst::BinOp {
        op: trust_ir::BinOp::Add,
        ty: Ty::U64,
        lhs: ValueId(31),
        rhs: ValueId(57),
    };
    f.blocks[0].body[2].inst = Inst::Return {
        values: vec![ValueId(81)],
    };
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}
fn subject(w: &RustU64AdditionModule<'_>, source: &str) -> connection::RawAdditionSubject {
    connection::RawAdditionSubject {
        original_source: source.into(),
        original_function: "identity".into(),
        original_instance: "standalone-syntax-model::identity:u64->u64;NOT-TCX".into(),
        module_bytes: w.original_bytes().to_vec(),
        ir_function_name: w.function_name().into(),
        function_id: w.function_id().index(),
        function_type_id: w.signature_id().index(),
        entry_block: w.entry_block().index(),
        parameter_value: w.parameter().index(),
        constant_value: w.constant().index(),
        literal: w.literal(),
        addition_value: w.addition().index(),
        return_value: w.returned().index(),
        reflected_context: w.reflected().context_term().clone(),
    }
}
fn proof(w: &RustU64AdditionModule<'_>) -> Expr {
    assert!(
        std::env::var_os("TRUST_G4_FORBID_PRODUCER").is_none(),
        "producer forbidden in fresh consumer"
    );
    let env = environment();
    let mut scope = LocalScope::new();
    let mut assem = Assembler::new(&mut scope, limits()).unwrap();
    let mut ps = Vec::new();
    let rho = assem.local(Expr::arrow(c("Nat"), c("Nat"))).unwrap();
    ps.push(rho.clone());
    let world = assem.local(Expr::type_()).unwrap();
    ps.push(world.clone());
    let mem = assem.local(c("IRByteMemoryV1")).unwrap();
    ps.push(mem.clone());
    let host = assem.local(world.term().clone()).unwrap();
    ps.push(host.clone());
    let providers = assem
        .local(a("IRByteProvidersV1", [world.term().clone()]))
        .unwrap();
    ps.push(providers.clone());
    let model = MachineModel::new(
        world.term().clone(),
        w.reflected(),
        providers.term().clone(),
    );
    let mut catalog = Catalog::new(env, w.reflected(), limits()).unwrap();
    let entry = catalog
        .rust_u64_add_literal_entry_v1(w.function_id())
        .unwrap();
    let memory_guard = EntryTarget::memory_admission(mem.term().clone());
    let memory_h = assem
        .local(eq(c("Bool"), memory_guard.clone(), c("Bool.true")))
        .unwrap();
    ps.push(memory_h.clone());
    let memory = PendingEquality::candidate(
        c("Bool"),
        memory_guard,
        c("Bool.true"),
        memory_h.term().clone(),
    );
    let word = Expr::app(rho.term().clone(), nat(0));
    let word_guard = a("ir_nat_ltb", [word.clone(), a("ir_nat_pow2", [nat(64)])]);
    let word_h = assem
        .local(eq(c("Bool"), word_guard, c("Bool.true")))
        .unwrap();
    ps.push(word_h.clone());
    let scalar = a("IRScalar.int_", [word.clone()]);
    let values = list("IRScalar", [scalar]);
    let fits = a(
        "ir_byte_value_matches_v1",
        [
            model.context().clone(),
            a("IRTy.uint_", [nat(64)]),
            a("IRScalar.int_", [word.clone()]),
        ],
    );
    let fits_proof = a(
        "ir_byte_u64_value_fits_v1",
        [model.context().clone(), word, word_h.term().clone()],
    );
    let values_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            fits,
            c("Bool.true"),
            fits_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let admitted = PendingEquality::candidate(
        c("Bool"),
        entry.admission(&model, values.clone()).unwrap(),
        c("Bool.true"),
        values_proof.clone(),
    );
    let initialized = entry
        .initialize(
            &mut assem,
            &model,
            values.clone(),
            mem.term().clone(),
            host.term().clone(),
            memory,
            admitted,
        )
        .unwrap();
    // Both scalar transfers retain the actual fetched instructions and SSA map.
    let coordinate = |pc| Coordinate {
        function: w.function_id(),
        block: w.entry_block(),
        instruction: pc,
    };
    let constant = catalog.fetch(coordinate(0)).unwrap();
    let k = nat(w.literal());
    let literal_value = a("IRScalar.int_", [k.clone()]);
    let checks = constant
        .scalar_checks(&model, initialized.current(), literal_value.clone())
        .unwrap();
    let evaluated = assem
        .conversion(
            c("IRStepResult"),
            checks.evaluation,
            a("IRStepResult.value", [literal_value.clone()]),
        )
        .unwrap();
    let operands = assem
        .conversion(c("Bool"), checks.operands, c("Bool.true"))
        .unwrap();
    let result = assem
        .conversion(c("Bool"), checks.result, c("Bool.true"))
        .unwrap();
    let cstep = constant
        .scalar_value(
            &mut assem,
            &model,
            initialized.current(),
            literal_value,
            trust_ir_build::core_execution::ScalarPremises {
                evaluated,
                operands,
                result,
                before: initialized.valid().clone(),
            },
        )
        .unwrap();
    assert_eq!(cstep.current().world, initialized.current().world);
    let word = Expr::app(rho.term().clone(), nat(0));
    let limit = a("ir_nat_pow2", [nat(64)]);
    let input_bound = a(
        "ir_byte_separation_lt_of_ltb_v1",
        [word.clone(), limit.clone(), word_h.term().clone()],
    );
    let k_bound = assem
        .conversion(
            c("Bool"),
            a("ir_nat_ltb", [k.clone(), limit.clone()]),
            c("Bool.true"),
        )
        .unwrap();
    let k_lt = a(
        "ir_byte_separation_lt_of_ltb_v1",
        [k.clone(), limit.clone(), k_bound.term().clone()],
    );
    let (_conditional, evaluated, _) = assem
        .byte_add_u64_canonical(
            word.clone(),
            k.clone(),
            trust_ir_build::core_execution::PendingProof::candidate(
                a("Nat.lt", [word.clone(), limit.clone()]),
                input_bound,
            ),
            trust_ir_build::core_execution::PendingProof::candidate(
                a("Nat.lt", [k.clone(), limit.clone()]),
                k_lt,
            ),
        )
        .unwrap();
    let output = a(
        "Nat.mod",
        [
            a("Nat.add", [word.clone(), k.clone()]),
            a("Nat.succ", [nat(u64::MAX)]),
        ],
    );
    let modulo = a(
        "RustSourceWord64IRV1.modCanonical",
        [
            nat(64),
            word.clone(),
            k.clone(),
            word_h.term().clone(),
            k_bound.term().clone(),
        ],
    );
    let conditional_scalar = evaluated.right().get_app_args()[0].clone();
    let conditional_word = conditional_scalar.get_app_args()[0].clone();
    let modulo_eq = PendingEquality::candidate(c("Nat"), output.clone(), conditional_word, modulo);
    let mapper = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        a("IRStepResult.value", [a("IRScalar.int_", [Expr::bvar(0)])]),
    );
    let mapped = assem
        .congruence_function(modulo_eq, c("IRStepResult"), mapper)
        .unwrap();
    let reversed = PendingEquality::candidate(
        c("IRStepResult"),
        mapped.right().clone(),
        mapped.left().clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                c("IRStepResult"),
                mapped.left().clone(),
                mapped.right().clone(),
                mapped.term().clone(),
            ],
        ),
    );
    let reversed = assem
        .convert_endpoints(
            reversed,
            evaluated.right().clone(),
            a("IRStepResult.value", [a("IRScalar.int_", [output.clone()])]),
        )
        .unwrap();
    let evaluated = assem.compose(evaluated, reversed).unwrap();
    let adding = catalog.fetch(coordinate(1)).unwrap();
    let output_scalar = a("IRScalar.int_", [output.clone()]);
    let checks = adding
        .scalar_checks(&model, cstep.current(), output_scalar.clone())
        .unwrap();
    let evaluated = assem
        .convert_endpoints(
            evaluated,
            checks.evaluation,
            a("IRStepResult.value", [output_scalar.clone()]),
        )
        .unwrap();
    let operand_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            a(
                "ir_byte_value_matches_v1",
                [
                    model.context().clone(),
                    a("IRTy.uint_", [nat(64)]),
                    a("IRScalar.int_", [word.clone()]),
                ],
            ),
            a(
                "ir_byte_value_matches_v1",
                [
                    model.context().clone(),
                    a("IRTy.uint_", [nat(64)]),
                    a("IRScalar.int_", [k.clone()]),
                ],
            ),
            a(
                "ir_byte_u64_value_fits_v1",
                [model.context().clone(), word.clone(), word_h.term().clone()],
            ),
            a(
                "ir_byte_u64_value_fits_v1",
                [model.context().clone(), k.clone(), k_bound.term().clone()],
            ),
        ],
    );
    let operands =
        PendingEquality::candidate(c("Bool"), checks.operands, c("Bool.true"), operand_proof);
    let out_lt = a(
        "Nat.mod_lt",
        [
            a("Nat.add", [word, k]),
            a("Nat.succ", [nat(u64::MAX)]),
            a("Nat.zero_lt_succ", [nat(u64::MAX)]),
        ],
    );
    let out_fits = a("ir_byte_ltb_of_lt_v1", [output.clone(), limit, out_lt]);
    let fit = a(
        "ir_byte_value_matches_v1",
        [
            model.context().clone(),
            a("IRTy.uint_", [nat(64)]),
            output_scalar.clone(),
        ],
    );
    let fits_proof = a(
        "ir_byte_u64_value_fits_v1",
        [model.context().clone(), output.clone(), out_fits],
    );
    let output_values_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            fit,
            c("Bool.true"),
            fits_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let result = PendingEquality::candidate(
        c("Bool"),
        checks.result,
        c("Bool.true"),
        output_values_proof.clone(),
    );
    let astep = adding
        .scalar_value(
            &mut assem,
            &model,
            cstep.current(),
            output_scalar.clone(),
            trust_ir_build::core_execution::ScalarPremises {
                evaluated,
                operands,
                result,
                before: cstep.valid().clone(),
            },
        )
        .unwrap();
    assert_eq!(astep.current().world, initialized.current().world);
    let values = list("IRScalar", [output_scalar]);
    let values_proof = output_values_proof;
    let owner = a("ir_byte_fresh_owner_v1", [mem.term().clone()]);
    let frame = RootReturnFrame {
        returning: astep.current().frame.clone(),
        legacy_memory: list("IRMemSlot", []),
        legacy_cursor: nat(0),
        memory: mem.term().clone(),
        host: host.term().clone(),
        owner: owner.clone(),
        next: a("Nat.succ", [owner]),
    };
    let site = catalog
        .fetch(Coordinate {
            function: w.function_id(),
            block: w.entry_block(),
            instruction: 2,
        })
        .unwrap();
    let target = catalog.call_target(w.function_id()).unwrap();
    let resolved = assem
        .conversion(
            a("IRList", [c("IRScalar")]),
            a(
                "ir_resolve",
                [
                    frame.current(&model).machine(),
                    list("Nat", [nat(w.returned().index() as u64)]),
                ],
            ),
            values.clone(),
        )
        .unwrap();
    let return_guard = site
        .root_return_admission(&model, &target, &frame, values.clone())
        .unwrap();
    let value_guard = a(
        "ir_byte_values_match_v1",
        [
            model.context().clone(),
            list("IRTy", [a("IRTy.uint_", [nat(64)])]),
            values,
        ],
    );
    let return_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            value_guard,
            c("Bool.true"),
            values_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let returned = site
        .return_from_root(
            &mut assem,
            &model,
            &target,
            &frame,
            resolved,
            PendingEquality::candidate(c("Bool"), return_guard, c("Bool.true"), return_proof),
            astep.valid().clone(),
        )
        .unwrap();
    let initialization = assem
        .congruence_function(
            initialized.equality().clone(),
            model.config_type(),
            model.run_function(&NatTerm::literal(3)),
        )
        .unwrap();
    let prefix = assem
        .concatenate(cstep.run().clone(), astep.run().clone())
        .unwrap();
    let whole = assem.concatenate(prefix, returned.run().clone()).unwrap();
    // Preserve the original proof term, but expose the definitionally equal
    // run3 endpoint across beta reduction and concatenated literal fuel.
    // Independent final kernel replay must check this conversion as well.
    let initialization = assem
        .convert_endpoints(
            initialization,
            model.run(&NatTerm::literal(3), initialized.equality().left().clone()),
            whole.equality().left().clone(),
        )
        .unwrap();
    let full = assem
        .compose(initialization, whole.equality().clone())
        .unwrap();
    let mut term = full.term().clone();
    for p in ps.iter().rev() {
        term = p.lam(term);
    }
    drop(assem);
    let term = scope.close(&term).unwrap();
    let actual = connection::ir_claim(&subject(
        w,
        &format!(
            "fn identity(x:u64)->u64 {{ x.wrapping_add({}) }}",
            w.literal()
        ),
    ))
    .unwrap();
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&term, &actual).unwrap();
    assert!(!tc.heartbeat_spent());
    term
}

#[test]
fn actual_original_addition_full64_entry_ssa_and_retired_world(
) -> std::result::Result<(), Box<dyn std::error::Error>> {
    let m = module_fn(7);
    let w = RustU64AdditionModule::from_module(&m, FuncId(41), 4096).unwrap();
    let expected = subject(&w, "fn identity(x:u64)->u64 { x.wrapping_add(7) }");
    let ir = proof(&w);
    let candidate = connection::candidate(&expected, ir.clone()).unwrap();
    let packet = connection::AdditionPacket {
        subject: expected.clone(),
        proof: candidate,
    };
    let checked = connection::replay(&expected, &packet).unwrap();
    assert_eq!(checked.subject().literal, 7);
    assert_eq!(w.parameter(), ValueId(31));
    assert_eq!(w.constant(), ValueId(57));
    assert_eq!(w.addition(), ValueId(81));
    // The raw mathematics cannot choose the independently derived full subject.
    for which in 0..14 {
        let mut changed = expected.clone();
        match which {
            0 => changed.original_source.push(' '),
            1 => changed.original_function.push('x'),
            2 => changed.original_instance.push('x'),
            3 => changed.module_bytes.push(0),
            4 => changed.ir_function_name.push('x'),
            5 => changed.function_id += 1,
            6 => changed.function_type_id += 1,
            7 => changed.entry_block += 1,
            8 => changed.parameter_value += 1,
            9 => changed.constant_value += 1,
            10 => changed.literal += 1,
            11 => changed.addition_value += 1,
            12 => changed.return_value += 1,
            _ => changed.reflected_context = c("Nat"),
        }
        let hostile = connection::AdditionPacket {
            subject: changed,
            proof: checked.proof().clone(),
        };
        assert!(connection::replay(&expected, &hostile)
            .unwrap_err()
            .contains("subject mismatch"));
    }
    let goal = connection::ir_claim(&expected).unwrap();
    // Correctly typed changed endpoint, not a timeout or missing proof.
    let unwrapped = map_endpoint(&goal, &|end| {
        replace(
            end,
            &c("Nat.mod"),
            &Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(1)),
            ),
        )
    });
    rejected(&ir, &unwrapped);
    let wrong_counter = map_endpoint(&goal, &|end| {
        let mut e = end.get_app_args().into_iter().cloned().collect::<Vec<_>>();
        let mut world = e[2].get_app_args().into_iter().cloned().collect::<Vec<_>>();
        // Use the original pre-memory in fresh_owner, not the retired output.
        let old_next = e[2].get_app_args()[4].clone();
        world[4] = old_next.get_app_args()[0].clone();
        e[2] = Expr::apps(end.get_app_args()[2].get_app_fn().clone(), world);
        Expr::apps(end.get_app_fn().clone(), e)
    });
    rejected(&ir, &wrong_counter);
    // An ACTUAL well-typed second original module computes +8. The full source
    // still says +7, so a newly produced valid +8 execution proof cannot close it.
    let m8 = module_fn(8);
    assert!(trust_ir_build::validate_module(&m8).is_empty());
    let w8 = RustU64AdditionModule::from_module(&m8, FuncId(41), 4096).unwrap();
    let ir8 = proof(&w8);
    let mut false_subject = subject(&w8, "fn identity(x:u64)->u64 { x.wrapping_add(7) }");
    false_subject.literal = 7;
    rejected(&ir8, &connection::ir_claim(&false_subject).unwrap());
    let false_proof = connection::candidate(&false_subject, ir8).unwrap();
    rejected(&false_proof, &connection::claim(&false_subject).unwrap());
    inhabited(&w, &ir);
    if let Ok(dir) = std::env::var("TRUST_G4_ADDITION_OUT") {
        let d = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&d)?;
        for (name, term) in [
            ("ir-proof", ir),
            ("claim", checked.claim().clone()),
            ("proof", checked.proof().clone()),
        ] {
            std::fs::write(d.join(format!("{name}.json")), serde_json::to_vec(&term)?)?;
        }
        std::fs::write(d.join("original-module.bin"), w.original_bytes())?;
    }
    Ok(())
}
#[test]
fn arithmetic_original_modulo_connection_all_u64_inputs_no_answer_premise() {
    let env = environment();
    let n = Expr::fvar(clean_kernel::expr::FVarId::new(0));
    let bound = Expr::fvar(clean_kernel::expr::FVarId::new(1));
    let guard = eq(
        c("Bool"),
        a("ir_nat_ltb", [n.clone(), a("ir_nat_pow2", [nat(64)])]),
        c("Bool.true"),
    );
    let tc = TypeChecker::new(env);
    for k in [0, 1, 7, u64::MAX] {
        let kb = refl(c("Bool"), c("Bool.true"));
        let t = a(
            "RustSourceWord64IRV1.modCanonical",
            [nat(64), n.clone(), nat(k), bound.clone(), kb],
        );
        let t = Expr::lam(
            BinderInfo::Default,
            guard.clone(),
            t.abstract_fvar(clean_kernel::expr::FVarId::new(1)),
        );
        let t = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            t.abstract_fvar(clean_kernel::expr::FVarId::new(0)),
        );
        let ty = tc.infer_type(&t).unwrap();
        assert!(!ty.has_fvar_quick());
        assert!(!ty.has_loose_bvars());
        tc.check_type(&t, &ty).unwrap();
    }
    assert!(!tc.heartbeat_spent());
}

fn rejected(proof: &Expr, goal: &Expr) {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(goal, &Expr::sort(Level::zero())).unwrap();
    let e = tc
        .check_type(proof, goal)
        .expect_err("changed original statement must reject");
    assert!(
        matches!(e, clean_kernel::TypeError::TypeMismatch { .. }),
        "semantic TypeMismatch required: {e:?}"
    );
    assert!(!tc.heartbeat_spent());
    if let Ok(dir) = std::env::var("TRUST_G4_ADDITION_OUT") {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&d).unwrap();
        std::fs::write(
            d.join(format!("negative-{n}-goal.json")),
            serde_json::to_vec(goal).unwrap(),
        )
        .unwrap();
        std::fs::write(d.join(format!("negative-{n}-error.txt")), format!("{e:?}")).unwrap();
    }
}
fn replace(term: &Expr, from: &Expr, to: &Expr) -> Expr {
    if term == from {
        return to.clone();
    }
    match term.kind() {
        ExprKind::App(f, x) => Expr::app(replace(f, from, to), replace(x, from, to)),
        ExprKind::Lam(b, t, x) => Expr::lam(*b, replace(t, from, to), replace(x, from, to)),
        ExprKind::Pi(b, t, x) => Expr::pi(*b, replace(t, from, to), replace(x, from, to)),
        _ => term.clone(),
    }
}
fn map_endpoint(goal: &Expr, map: &impl Fn(&Expr) -> Expr) -> Expr {
    if let ExprKind::Pi(b, t, x) = goal.kind() {
        return Expr::pi(*b, t.as_ref().clone(), map_endpoint(x, map));
    }
    let args = goal.get_app_args();
    assert_eq!(args.len(), 3);
    eq(args[0].clone(), args[1].clone(), map(args[2]))
}
fn inhabited(witness: &RustU64AdditionModule<'_>, term: &Expr) {
    let allocation = |base, size, owner, live| {
        a(
            "IRByteAllocationV1.mk",
            [nat(base), nat(size), nat(owner), c(live)],
        )
    };
    let mem = a(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                [
                    allocation(16, 8, 0, "Bool.true"),
                    allocation(48, 8, 7, "Bool.false"),
                ],
            ),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                a("IROption.none", [c("Nat")]),
            ),
            nat(128),
        ],
    );
    let memory_guard = EntryTarget::memory_admission(mem.clone());
    let tc = TypeChecker::new(environment());
    let hmem = refl(c("Bool"), c("Bool.true"));
    tc.check_type(&hmem, &eq(c("Bool"), memory_guard, c("Bool.true")))
        .unwrap();
    let providers = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        Expr::lam(
            BinderInfo::Default,
            a("IRList", [c("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                c("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    a(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            a("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    for word in [0, u64::MAX] {
        let rho = Expr::lam(BinderInfo::Default, c("Nat"), nat(word));
        let hword = refl(c("Bool"), c("Bool.true"));
        let instantiated = Expr::apps(
            term.clone(),
            [
                rho.clone(),
                c("Nat"),
                mem.clone(),
                nat(19),
                providers.clone(),
                hmem.clone(),
                hword.clone(),
            ],
        );
        let mut claim = connection::ir_claim(&subject(
            witness,
            "fn identity(x:u64)->u64 { x.wrapping_add(7) }",
        ))
        .unwrap();
        for value in [
            rho,
            c("Nat"),
            mem.clone(),
            nat(19),
            providers.clone(),
            hmem.clone(),
            hword,
        ] {
            let ExprKind::Pi(_, _, body) = claim.kind() else {
                panic!("quantified actual IR claim")
            };
            claim = body.instantiate(&value);
        }
        tc.check_type(&instantiated, &claim).unwrap();
    }
    assert!(!tc.heartbeat_spent());
}

#[test]
fn actual_module_witness_rejects_complete_wrong_shapes_and_preserves_other_profiles() {
    let baseline = module_fn(7);
    assert!(RustU64AdditionModule::from_module(&baseline, FuncId(41), 4096).is_ok());
    for mutation in 0..9 {
        let mut m = baseline.clone();
        let f = &mut m.functions[0];
        match mutation {
            0 => f.calling_conv = CallingConv::C,
            1 => f.calling_conv = CallingConv::Fast,
            2 => {
                if let Inst::BinOp { op, .. } = &mut f.blocks[0].body[1].inst {
                    *op = trust_ir::BinOp::Sub
                }
            }
            3 => {
                f.blocks[0].body[2].inst = Inst::Return {
                    values: vec![ValueId(31)],
                }
            }
            4 => {
                let extra = f.blocks[0].body[2].clone();
                f.blocks[0].body.push(extra)
            }
            5 => {
                if let Inst::BinOp { lhs, rhs, .. } = &mut f.blocks[0].body[1].inst {
                    std::mem::swap(lhs, rhs)
                }
            }
            6 => {
                f.blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::U64,
                    value: trust_ir::Constant::Int(-1),
                }
            }
            7 => f.entry = BlockId(19),
            _ => f.blocks[0].body[1].results = vec![ValueId(31)],
        }
        assert!(
            RustU64AdditionModule::from_module(&m, FuncId(41), 4096).is_err(),
            "mutation{mutation}"
        );
    }
    assert!(RustU64AdditionModule::from_module(&baseline, FuncId(42), 4096).is_err());
    assert!(
        trust_ir_build::source_identity_data::RustU64IdentityModule::from_module(
            &baseline,
            FuncId(41),
            4096
        )
        .is_err()
    );
    let mut cmod = baseline.clone();
    cmod.functions[0].calling_conv = CallingConv::C;
    assert!(
        trust_ir_build::core_reflection::reflect_core_module_v1(&cmod, &[(FuncId(41), 4096)])
            .is_ok()
    );
    assert!(trust_ir_build::core_reflection::reflect_core_module_v1(
        &baseline,
        &[(FuncId(41), 4096)]
    )
    .is_err());
}

#[test]
fn fresh_retained_original_proof_no_producer_and_real_wrong_module(
) -> std::result::Result<(), Box<dyn std::error::Error>> {
    assert_eq!(std::env::var("TRUST_G4_FORBID_PRODUCER").unwrap(), "1");
    let d = std::path::PathBuf::from(std::env::var("TRUST_G4_RETAINED_ADDITION_DIR").unwrap());
    let source = std::fs::read_to_string(d.join("original-source.rs")).unwrap();
    let bytes = std::fs::read(d.join("original-module.bin")).unwrap();
    // Existing canonical decoder supplies DATA only. The private witness must
    // still validate/refelect the exact original complete typed module itself.
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    let w = RustU64AdditionModule::from_module(&module, FuncId(41), 4096).unwrap();
    assert_eq!(w.original_bytes(), bytes);
    let expected = subject(&w, &source);
    let retained: Expr = read_retained_expr(&d.join("proof.json"));
    let retained_goal: Expr = read_retained_expr(&d.join("claim.json"));
    assert_eq!(connection::claim(&expected).unwrap(), retained_goal);
    let packet = connection::AdditionPacket {
        subject: expected.clone(),
        proof: retained,
    };
    let checked = connection::replay(&expected, &packet).unwrap();
    let ir: Expr = read_retained_expr(&d.join("ir-proof.json"));
    let goal = connection::ir_claim(&expected).unwrap();
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&ir, &goal).unwrap();
    assert!(!tc.heartbeat_spent());
    let mut wrong = expected.clone();
    wrong.function_id = 42;
    rejected(&ir, &connection::ir_claim(&wrong).unwrap());
    let m8 = module_fn(8);
    let w8 = RustU64AdditionModule::from_module(&m8, FuncId(41), 4096).unwrap();
    let mut wrong = subject(&w8, &source);
    wrong.literal = 7;
    rejected(&ir, &connection::ir_claim(&wrong).unwrap());
    let unwrapped = map_endpoint(&goal, &|end| {
        replace(
            end,
            &c("Nat.mod"),
            &Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(1)),
            ),
        )
    });
    rejected(&ir, &unwrapped);
    let dropped_world = map_endpoint(&goal, &|end| {
        let mut e = end.get_app_args().into_iter().cloned().collect::<Vec<_>>();
        let mut world = e[2].get_app_args().into_iter().cloned().collect::<Vec<_>>();
        let old_next = e[2].get_app_args()[4].clone();
        world[4] = old_next.get_app_args()[0].clone();
        e[2] = Expr::apps(end.get_app_args()[2].get_app_fn().clone(), world);
        Expr::apps(end.get_app_fn().clone(), e)
    });
    rejected(&ir, &dropped_world);
    let audit = environment().audit_certification(checked.claim(), checked.proof());
    assert!(audit.is_certified());
    for n in &audit.dependencies {
        for deps in [
            environment().axiom_deps(n),
            environment().foundational_axiom_deps(n),
            environment().trust_marker_deps(n),
        ] {
            assert!(deps.unwrap().is_empty(), "{n}");
        }
    }
    if let Ok(out) = std::env::var("TRUST_G4_ADDITION_OUT") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out)?;
        let proof_env = environment();
        let declarations = audit
            .dependencies
            .iter()
            .map(|name| {
                proof_env
                    .get_const(name)
                    .cloned()
                    .ok_or_else(|| format!("artifact dependency is undeclared: {name}"))
            })
            .collect::<std::result::Result<Vec<_>, String>>()?;
        let evidence = serde_json::json!({"producer_forbidden":true,"claim":checked.claim(),"proof":checked.proof(),"subject_bytes":w.original_bytes(),"source":source,"actual_module_function_id":w.function_id().index(),"parameter":w.parameter().index(),"constant":w.constant().index(),"literal":w.literal(),"addition":w.addition().index(),"returned":w.returned().index(),"dependencies":declarations,"scope":"Original source MODEL→actual typed IR logical body only; no TCX/frontend/physicalABI/NoUB/native/admission/proof-grade"});
        std::fs::write(
            out.join("fresh-replay.json"),
            serde_json::to_vec(&evidence)?,
        )?;
    }
    Ok(())
}
