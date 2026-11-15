// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked change of evaluation strategy for the reflected comparison family.
//!
//! Lean's native subtraction can recurse through a large numeral when the
//! minuend is symbolic. Guarding constructor inspection avoids that work, but
//! changes definitional equality, so the original definitions and their four
//! body-dependent agreement proofs are retained and checked separately. The
//! exported comparison and theorem images are connected by explicit equality
//! proofs, never by an axiom or a replacement assertion.
//!
//! The machine comparisons first peel one constructor from each operand, then
//! call `ir_nat_sub_ltb` / `ir_nat_sub_eqb`. Keep those actual stored wrappers:
//! guard the subtraction cores and lift their agreements through the two case
//! splits. Original wrapper proofs must refer to original core proofs, too.

use std::collections::{HashMap, HashSet};

use clean_kernel::{ConstantKind, Environment};

use crate::emit::emit_constant;
use crate::printer::{level_params_suffix, Printer};
use crate::{Item, ItemKind};

pub const COMPARISONS: [&str; 4] = [
    "ir_nat_sub_ltb",
    "ir_nat_ltb",
    "ir_nat_sub_eqb",
    "ir_nat_eqb",
];
pub const AGREEMENTS: [&str; 4] = [
    "ir_nat_sub_ltb_walk_eq",
    "ir_nat_ltb_walk_eq",
    "ir_nat_sub_eqb_walk_eq",
    "ir_nat_eqb_walk_eq",
];

fn original_renames(renames: &HashMap<String, String>) -> HashMap<String, String> {
    let mut originals = renames.clone();
    for name in COMPARISONS.into_iter().chain(AGREEMENTS) {
        originals.insert(name.to_string(), format!("ReplayBridge.{name}Original"));
    }
    originals
}

fn reference_walk(comparison: &str) -> Result<&'static str, String> {
    match comparison {
        "ir_nat_sub_ltb" | "ir_nat_ltb" => Ok("ir_nat_ltb_walk"),
        "ir_nat_sub_eqb" | "ir_nat_eqb" => Ok("ir_nat_eqb_walk"),
        _ => Err(format!("missing comparison reference walk: {comparison}")),
    }
}

/// Independent equality with native subtraction, including open operands.
/// This helper does not replace `Nat.sub`: its recursive equations remain
/// available to the rest of the metatheory exactly as before.
pub const GUARDED_SUBTRACTION: &str = r#"
-- ==== checked evaluation guard for reflected comparisons ====
noncomputable def CleanVerify.ReplayBridge.sub (a b : CleanVerify.Nat) : CleanVerify.Nat :=
  @_root_.Nat.casesOn (fun _ => _root_.Nat) b a
    (fun _ => @_root_.Nat.casesOn (fun _ => _root_.Nat) a 0
      (fun _ => _root_.Nat.sub a b))

theorem CleanVerify.ReplayBridge.sub_agrees (a b : CleanVerify.Nat) :
    CleanVerify.ReplayBridge.sub a b = CleanVerify.Nat.sub a b := by
  cases b with
  | zero => rfl
  | succ b =>
    cases a with
    | zero => exact (_root_.Nat.zero_sub (b + 1)).symm
    | succ a => rfl

#print axioms CleanVerify.ReplayBridge.sub_agrees

"#;

fn ordinary_item(env: &Environment, item: &Item) -> Result<Item, String> {
    let ci = env
        .get_const(&item.name)
        .ok_or_else(|| "comparison bridge constant is missing".to_string())?;
    if ci.value.is_none() {
        return Err("comparison bridge requires a checked value".to_string());
    }
    Ok(Item {
        name: item.name.clone(),
        kind: if ci.kind == ConstantKind::Theorem {
            ItemKind::Theorem
        } else {
            ItemKind::Def
        },
    })
}

pub(super) fn emit_comparison(
    env: &Environment,
    item: &Item,
    renames: &HashMap<String, String>,
    structs: &HashSet<String>,
) -> Result<String, String> {
    let name = item.name.to_string();
    if !COMPARISONS.contains(&name.as_str()) {
        return Err(format!("unsupported comparison bridge: {name}"));
    }
    let ordinary = ordinary_item(env, item)?;
    let original_renames = original_renames(renames);
    let original = emit_constant(env, &ordinary, &original_renames, structs)?;

    let mut guarded_renames = renames.clone();
    guarded_renames.insert("Nat.sub".to_string(), "ReplayBridge.sub".to_string());
    let guarded = emit_constant(env, &ordinary, &guarded_renames, structs)?;
    let agreement = match name.as_str() {
        "ir_nat_sub_ltb" => {
            "_root_.congrArg CleanVerify.ir_nat_pos (CleanVerify.ReplayBridge.sub_agrees b a)"
        }
        "ir_nat_sub_eqb" => {
            "_root_.Eq.trans\n\
             (_root_.congrArg\n\
               (fun u => @CleanVerify.Bool.rec (fun _ => CleanVerify.Bool)\n\
                 CleanVerify.Bool.false (CleanVerify.ir_nat_iszero (CleanVerify.ReplayBridge.sub b a))\n\
                 (CleanVerify.ir_nat_iszero u))\n\
               (CleanVerify.ReplayBridge.sub_agrees a b))\n\
             (_root_.congrArg\n\
               (fun v => @CleanVerify.Bool.rec (fun _ => CleanVerify.Bool)\n\
                 CleanVerify.Bool.false (CleanVerify.ir_nat_iszero v)\n\
                 (CleanVerify.ir_nat_iszero (CleanVerify.Nat.sub a b)))\n\
               (CleanVerify.ReplayBridge.sub_agrees b a))"
        }
        "ir_nat_ltb" => {
            "by\n\
             \x20 cases a with\n\
             \x20 | zero => rfl\n\
             \x20 | succ a =>\n\
             \x20   cases b with\n\
             \x20   | zero => rfl\n\
             \x20   | succ b => exact CleanVerify.ReplayBridge.ir_nat_sub_ltb_agrees a b"
        }
        "ir_nat_eqb" => {
            "by\n\
             \x20 cases a with\n\
             \x20 | zero => rfl\n\
             \x20 | succ a =>\n\
             \x20   cases b with\n\
             \x20   | zero => rfl\n\
             \x20   | succ b => exact CleanVerify.ReplayBridge.ir_nat_sub_eqb_agrees a b"
        }
        _ => return Err(format!("missing comparison agreement proof: {name}")),
    };

    Ok(format!(
        "-- Original stored comparison body, then its proved evaluation-strategy image.\n\
         {original}\n{guarded}\n\
         theorem CleanVerify.ReplayBridge.{name}_agrees (a b : CleanVerify.Nat) :\n\
           CleanVerify.{name} a b = CleanVerify.ReplayBridge.{name}Original a b :=\n\
           {agreement}\n\
         #print axioms CleanVerify.ReplayBridge.{name}_agrees\n"
    ))
}

pub(super) fn emit_agreement(
    env: &Environment,
    item: &Item,
    renames: &HashMap<String, String>,
    structs: &HashSet<String>,
) -> Result<String, String> {
    let name = item.name.to_string();
    if !AGREEMENTS.contains(&name.as_str()) {
        return Err(format!("unsupported comparison proof transport: {name}"));
    }
    let op = name
        .strip_suffix("_walk_eq")
        .ok_or_else(|| format!("comparison agreement name is malformed: {name}"))?;
    let ordinary = ordinary_item(env, item)?;
    let walk = reference_walk(op)?;
    let original_renames = original_renames(renames);
    let original = emit_constant(env, &ordinary, &original_renames, structs)?;
    let ci = env
        .get_const(&item.name)
        .ok_or_else(|| "comparison agreement is missing".to_string())?;
    let mut printer = Printer::new(renames, structs);
    let ty = printer.expr(&ci.type_, &mut Vec::new())?;
    let suffix = level_params_suffix(&ci.level_params);
    let keyword = match ci.kind {
        ConstantKind::Theorem => "theorem",
        ConstantKind::Opaque => "noncomputable opaque",
        _ => "noncomputable def",
    };
    Ok(format!(
        "-- The original stored proof is rechecked before equality transport.\n\
         {original}\n\
         {keyword} CleanVerify.{name}{suffix} : {ty} :=\n\
           fun a b => _root_.Eq.mpr\n\
             (_root_.congrArg (fun r => @CleanVerify.Eq CleanVerify.Bool r\n\
               (@CleanVerify.{walk} a b))\n\
               (@CleanVerify.ReplayBridge.{op}_agrees a b))\n\
             (@CleanVerify.ReplayBridge.{name}Original a b)\n\
         #print axioms CleanVerify.{name}\n"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_family_renames_preserve_core_proof_dependencies() {
        let mut existing = HashMap::new();
        existing.insert("unrelated".to_string(), "renamed".to_string());
        let originals = original_renames(&existing);
        for name in COMPARISONS.into_iter().chain(AGREEMENTS) {
            assert_eq!(
                originals.get(name),
                Some(&format!("ReplayBridge.{name}Original"))
            );
        }
        assert_eq!(originals.get("unrelated"), Some(&"renamed".to_string()));
        assert!(!originals.contains_key("Nat.sub"));
    }

    #[test]
    fn subtraction_cores_share_the_actual_wrapper_reference_walks() {
        for (comparison, agreement) in COMPARISONS.into_iter().zip(AGREEMENTS) {
            assert_eq!(agreement, format!("{comparison}_walk_eq"));
            assert!(matches!(
                reference_walk(comparison),
                Ok("ir_nat_ltb_walk" | "ir_nat_eqb_walk")
            ));
        }
        assert_eq!(
            reference_walk("ir_nat_sub_ltb"),
            reference_walk("ir_nat_ltb")
        );
        assert_eq!(
            reference_walk("ir_nat_sub_eqb"),
            reference_walk("ir_nat_eqb")
        );
        assert!(reference_walk("ir_nat_leb").is_err());
    }
}
