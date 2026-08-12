use super::*;
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

#[test]
fn test_instance_table_basic() {
    let mut table = InstanceTable::new();

    // Register a class
    let add_class = Name::from_string("Add");
    table.register_class(add_class.clone(), 1, vec![]);
    assert!(table.is_class(&add_class));
    assert_eq!(table.num_classes(), 1);

    // Add an instance
    let nat = Name::from_string("Nat");
    let inst_name = Name::from_string("instAddNat");
    let inst_expr = Expr::const_(inst_name.clone(), vec![]);
    let inst_type = Expr::app(
        Expr::const_(add_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    table.add_instance(
        inst_name.clone(),
        add_class.clone(),
        inst_expr,
        inst_type,
        DEFAULT_PRIORITY,
    );

    let instances = table.get_instances(&add_class);
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].name, inst_name);
}

#[test]
fn test_instance_priority_ordering() {
    let mut table = InstanceTable::new();

    let class_name = Name::from_string("Show");
    table.register_class(class_name.clone(), 1, vec![]);

    // Add instances with different priorities
    table.add_instance(
        Name::from_string("low"),
        class_name.clone(),
        Expr::const_(Name::from_string("low"), vec![]),
        Expr::const_(class_name.clone(), vec![]),
        50,
    );
    table.add_instance(
        Name::from_string("high"),
        class_name.clone(),
        Expr::const_(Name::from_string("high"), vec![]),
        Expr::const_(class_name.clone(), vec![]),
        150,
    );
    table.add_instance(
        Name::from_string("default"),
        class_name.clone(),
        Expr::const_(Name::from_string("default"), vec![]),
        Expr::const_(class_name.clone(), vec![]),
        100,
    );

    let instances = table.get_instances(&class_name);
    assert_eq!(instances.len(), 3);
    assert_eq!(instances[0].name, Name::from_string("high"));
    assert_eq!(instances[1].name, Name::from_string("default"));
    assert_eq!(instances[2].name, Name::from_string("low"));
}

#[test]
fn test_equal_priority_preserves_feed_order() {
    // Tie-break contract (B99): `add_instance` inserts a new instance
    // AFTER existing entries of the SAME priority (`position(<)`), i.e.
    // the table preserves the feed order within a tier. The kernel env
    // registry feeds `init_instances_from_env` most-recent-FIRST within a
    // tier (`register_instance` inserts before `<=`), so the elaborated
    // table order is: priority desc, then most-recent-first — the
    // Lean-faithful order `candidate_order`'s ascending-index tiebreak
    // then consumes.
    let mut table = InstanceTable::new();
    let class_name = Name::from_string("Tie");
    table.register_class(class_name.clone(), 1, vec![]);

    // Simulate the kernel-env feed for: `older` declared first, `newer`
    // declared second, both at DEFAULT_PRIORITY. The env registry yields
    // them newest-first, so the table receives `newer` then `older`.
    for name in ["newer", "older"] {
        table.add_instance(
            Name::from_string(name),
            class_name.clone(),
            Expr::const_(Name::from_string(name), vec![]),
            Expr::const_(class_name.clone(), vec![]),
            DEFAULT_PRIORITY,
        );
    }
    // A higher-priority instance still dominates both, regardless of feed
    // position.
    table.add_instance(
        Name::from_string("high"),
        class_name.clone(),
        Expr::const_(Name::from_string("high"), vec![]),
        Expr::const_(class_name.clone(), vec![]),
        DEFAULT_PRIORITY + 1,
    );

    let names: Vec<String> = table
        .get_instances(&class_name)
        .iter()
        .map(|i| i.name.to_string())
        .collect();
    assert_eq!(
        names,
        vec!["high", "newer", "older"],
        "table order must be priority desc, then feed order (newest first) within a tier"
    );
}

#[test]
fn test_default_priority_is_lean_default() {
    // Lean fidelity pin: default 1000 sits strictly between `low` (100)
    // and `high` (10000), so `(priority := low)` LOSES to an unannotated
    // instance and `(priority := high)` beats one (B99).
    assert_eq!(DEFAULT_PRIORITY, 1000);
}

#[test]
fn test_extract_class_app() {
    // Test Add Nat
    let add = Name::from_string("Add");
    let nat = Name::from_string("Nat");
    let ty = Expr::app(
        Expr::const_(add.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    let result = extract_class_app(&ty);
    let (class_name, args) = result.expect("extract_class_app should find Add Nat");
    assert_eq!(class_name, add);
    assert_eq!(args.len(), 1);
    assert!(matches!(args[0].kind(), ExprKind::Const(n, _) if *n == nat));
}

#[test]
fn test_extract_class_app_multiple_args() {
    // Test Functor F A
    let functor = Name::from_string("Functor");
    let f = Name::from_string("F");
    let a = Name::from_string("A");

    let ty = Expr::app(
        Expr::app(
            Expr::const_(functor.clone(), vec![]),
            Expr::const_(f.clone(), vec![]),
        ),
        Expr::const_(a.clone(), vec![]),
    );

    let result = extract_class_app(&ty);
    let (class_name, args) = result.expect("extract_class_app should find Functor F A");
    assert_eq!(class_name, functor);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_extract_class_app_no_args() {
    // Test bare class name
    let inhabited = Name::from_string("Inhabited");
    let ty = Expr::const_(inhabited.clone(), vec![]);

    let result = extract_class_app(&ty);
    let (class_name, args) = result.expect("extract_class_app should find bare Inhabited");
    assert_eq!(class_name, inhabited);
    assert_eq!(args.len(), 0);
}

#[test]
fn test_extract_class_app_non_class() {
    // Test non-constant head (e.g., a BVar)
    let ty = Expr::bvar(0);
    assert!(
        extract_class_app(&ty).is_none(),
        "BVar should not be a class app"
    );

    // Test Sort
    let ty = Expr::sort(Level::zero());
    assert!(
        extract_class_app(&ty).is_none(),
        "Sort should not be a class app"
    );
}

#[test]
fn test_class_with_out_params() {
    let mut table = InstanceTable::new();

    // Register OutParam-style class like `Functor`
    let functor = Name::from_string("Functor");
    table.register_class(functor.clone(), 1, vec![0]); // F is an out-param

    let info = table.get_class(&functor).unwrap();
    assert_eq!(info.num_params, 1);
    assert_eq!(info.out_params, vec![0]);
}
