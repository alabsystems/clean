//! Exact generated instance identities; diagnostic displays never become Names.

use clean_kernel::{name::NameInner, Name};

#[derive(Clone, Copy)]
enum Family {
    BuiltinTypeFirst,
    LegacyClassFirst,
    SourceHandler,
}

fn components(name: &Name) -> Vec<&NameInner> {
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            part @ (NameInner::Str(parent, _) | NameInner::Num(parent, _)) => {
                parts.push(part);
                current = parent;
            }
        }
    }
    parts.reverse();
    parts
}

fn append_parts(mut prefix: Name, parts: &[&NameInner]) -> Name {
    for part in parts {
        prefix = match part {
            NameInner::Str(_, text) => prefix.str(text.as_ref()),
            NameInner::Num(_, number) => prefix.num(*number),
            NameInner::Anon => unreachable!("component collector excludes the root"),
        };
    }
    prefix
}

/// Exact finite builtin identities; lexical escaping does not change identity.
pub(crate) fn builtin_class(name: &Name) -> Option<&'static str> {
    [
        "BEq",
        "Repr",
        "Hashable",
        "Inhabited",
        "DecidableEq",
        "Ord",
        "Nonempty",
        "ToString",
        "Functor",
        "Foldable",
        "Traversable",
    ]
    .into_iter()
    .find(|text| name == &Name::anon().str(text))
}

/// Preserve ordinary historical spelling without ever flattening components.
/// Numeric names and source-handler boundaries use a length-framed identity.
///
/// A `private` target (`_private.<module>.0.Col`) is named by its user-facing
/// name: Lean 4.8.0 names the instance of `private inductive Col deriving
/// DecidableEq` `instDecidableEqCol`, a PUBLIC name, so two sibling modules
/// deriving for their own private `Col` collide in an importer, which Lean
/// refuses ("environment already contains 'instDecidableEqCol.proof_2'",
/// G21 B3 review probe `Pkg/DC`). Framing the mangled name instead gave each
/// sibling its own instance and accepted that importer.
fn generated_name(class: &Name, target: &Name, family: Family) -> Name {
    let target = crate::private_names::user_facing_name(target);
    let class_parts = components(class);
    let target_parts = components(&target);
    let conventional = !matches!(family, Family::SourceHandler)
        && !target_parts.is_empty()
        && target_parts.iter().all(|p| matches!(p, NameInner::Str(..)));
    if let Some(label) = builtin_class(class).filter(|_| conventional) {
        let last = target_parts.len() - 1;
        let mut result = Name::anon();
        for (index, part) in target_parts.iter().enumerate() {
            let NameInner::Str(_, text) = part else {
                unreachable!()
            };
            let mut component = String::new();
            if index == 0 {
                component.push_str("inst");
                if matches!(family, Family::LegacyClassFirst) {
                    component.push_str(label);
                }
            }
            component.push_str(text);
            if index == last && matches!(family, Family::BuiltinTypeFirst) {
                component.push_str(label);
            }
            result = result.str(component);
        }
        return result;
    }
    // Leading Num makes framed names disjoint from the all-Str conventional
    // family. Lengths frame both original typed sequences, even when either
    // contains a Num equal to a framing number. No hash or display is used.
    let tag = match family {
        Family::BuiltinTypeFirst => 0,
        Family::LegacyClassFirst => 1,
        Family::SourceHandler => 2,
    };
    let mut result = Name::anon()
        .num(0x5452_4452)
        .num(tag)
        .num(u64::try_from(class_parts.len()).expect("Name allocation length fits u64"));
    result = append_parts(result, &class_parts);
    result =
        result.num(u64::try_from(target_parts.len()).expect("Name allocation length fits u64"));
    append_parts(result, &target_parts)
}

pub(crate) fn builtin_instance_name(target: &Name, class: &'static str) -> Name {
    generated_name(&Name::anon().str(class), target, Family::BuiltinTypeFirst)
}

pub(crate) fn legacy_builtin_instance_name(class: &str, target: &Name) -> Name {
    // This compatibility entry has fixed compiler builtin callers. Treat even
    // an unexpected label as one Str; do not infer a path from punctuation.
    generated_name(&Name::anon().str(class), target, Family::LegacyClassFirst)
}

pub(crate) fn source_handler_instance_name(class: &Name, target: &Name) -> Name {
    generated_name(class, target, Family::SourceHandler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conventional_names_preserve_component_boundaries() {
        assert_eq!(
            builtin_instance_name(&Name::anon().str("Counter"), "BEq"),
            Name::anon().str("instCounterBEq")
        );
        assert_eq!(
            builtin_instance_name(&Name::anon().str("A").str("B"), "BEq"),
            Name::anon().str("instA").str("BBEq")
        );
        assert_eq!(
            builtin_instance_name(&Name::anon().str("A.B"), "BEq"),
            Name::anon().str("instA.BBEq")
        );
        assert_ne!(
            builtin_instance_name(&Name::anon().str("A.B"), "BEq"),
            builtin_instance_name(&Name::anon().str("A").str("B"), "BEq")
        );
        assert_eq!(
            legacy_builtin_instance_name("BEq", &Name::anon().str("Counter")),
            Name::anon().str("instBEqCounter")
        );
    }

    #[test]
    fn frame_retains_numeric_and_class_target_boundaries() {
        let str_seven = Name::anon().str("7");
        let num_seven = Name::anon().num(7);
        assert_ne!(
            builtin_instance_name(&str_seven, "BEq"),
            builtin_instance_name(&num_seven, "BEq")
        );
        let c = Name::anon().str("C");
        assert_ne!(
            source_handler_instance_name(&c, &str_seven),
            source_handler_instance_name(&c, &num_seven)
        );
        assert_ne!(
            source_handler_instance_name(&Name::anon().str("A"), &Name::anon().str("BC")),
            source_handler_instance_name(&Name::anon().str("AB"), &Name::anon().str("C"))
        );
        assert_ne!(
            source_handler_instance_name(&Name::anon().str("A.B"), &c),
            source_handler_instance_name(&Name::anon().str("A").str("B"), &c)
        );
        assert_ne!(
            source_handler_instance_name(&Name::anon().str("A").num(1), &c),
            source_handler_instance_name(&Name::anon().str("A"), &Name::anon().num(1).str("C"))
        );
        assert_ne!(
            source_handler_instance_name(&Name::anon().str("BEq"), &str_seven),
            builtin_instance_name(&str_seven, "BEq")
        );
    }

    #[test]
    fn generated_names_have_no_collisions_in_adversarial_typed_population() {
        let names = [
            Name::anon(),
            Name::anon().str(""),
            Name::anon().str("A"),
            Name::anon().str("A.B"),
            Name::anon().str("A").str("B"),
            Name::anon().str("7"),
            Name::anon().num(7),
            Name::anon().num(2).str("A"),
            Name::anon().str("A").num(2),
            Name::anon().str("A").num(2).str("B"),
        ];
        let mut seen = std::collections::HashMap::new();
        for (ci, class) in names.iter().enumerate() {
            for (ti, target) in names.iter().enumerate() {
                let output = source_handler_instance_name(class, target);
                assert!(seen.insert(output, (ci, ti)).is_none());
            }
        }
        let classes = [
            "BEq",
            "Repr",
            "Hashable",
            "Inhabited",
            "DecidableEq",
            "Ord",
            "Nonempty",
            "ToString",
            "Functor",
            "Foldable",
            "Traversable",
        ];
        let mut seen = std::collections::HashMap::new();
        for class in classes {
            for (ti, target) in names.iter().enumerate() {
                assert!(seen
                    .insert(builtin_instance_name(target, class), (class, ti))
                    .is_none());
            }
        }
    }
}
