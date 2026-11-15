// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Syntactic mutation of instances. Mutants are cheap; the parser and checker discard the
//! ill-formed ones, and every accepted mutant is judged semantically.

use crate::model::Rng;
use crate::oracle::Instance;
use crate::sexp::{self, Sx};

const OP_CLASSES: &[&[&str]] = &[
    &["and", "or", "xor", "=>", "="],
    &["+", "-", "*"],
    &["div", "mod"],
    &["<", "<=", ">", ">=", "="],
    &[
        "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl",
        "bvlshr", "bvashr", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
    ],
    &[
        "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ],
    &["bvnot", "bvneg"],
    &["str.prefixof", "str.suffixof", "str.contains"],
    &["str.<", "str.<="],
    &["str.replace", "str.replace_all"],
    &["str.len", "str.to_code", "str.to_int"],
    &["re.union", "re.inter", "re.++", "re.diff"],
    &["re.*", "re.+", "re.opt", "re.comp"],
    &["forall", "exists"],
    &[
        "extract",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "repeat",
    ],
    &["to_real", "abs", "-"],
    &["ubv_to_int", "sbv_to_int"],
];

const EXTRA_ATOMS: &[&str] = &[
    "0", "1", "2", "3", "(- 1)", "(- 2)", "0.0", "0.5", "1.0", "1.5", "(- 0.5)", "#b0", "#b1",
    "#b00", "#b01", "#b10", "#b11", "#b0000", "#b0001", "#b1000", "#b0111", "#b1111", "true",
    "false", "\"\"", "\"a\"", "\"ab\"", "\"b\"",
];

pub const RULES: &[&str] = &[
    "true",
    "false",
    "not_not",
    "and_pos",
    "and_neg",
    "or_pos",
    "or_neg",
    "xor_pos1",
    "xor_pos2",
    "xor_neg1",
    "xor_neg2",
    "implies_pos",
    "implies_neg1",
    "implies_neg2",
    "equiv_pos1",
    "equiv_pos2",
    "equiv_neg1",
    "equiv_neg2",
    "ite_pos1",
    "ite_pos2",
    "ite_neg1",
    "ite_neg2",
    "eq_reflexive",
    "eq_transitive",
    "eq_congruent",
    "eq_congruent_pred",
    "distinct_elim",
    "la_rw_eq",
    "la_generic",
    "bounded_farkas",
    "la_disequality",
    "la_totality",
    "la_tautology",
    "poly_simp",
    "poly_simp_rel",
    "forall_inst",
    "qnt_join",
    "qnt_rm_unused",
    "resolution",
    "th_resolution",
    "refl",
    "strict_refl",
    "trans",
    "cong",
    "ho_cong",
    "and_intro",
    "and",
    "tautology",
    "not_or",
    "or",
    "not_and",
    "xor1",
    "xor2",
    "not_xor1",
    "not_xor2",
    "implies",
    "not_implies1",
    "not_implies2",
    "equiv1",
    "equiv2",
    "not_equiv1",
    "not_equiv2",
    "ite1",
    "ite2",
    "not_ite1",
    "not_ite2",
    "ite_intro",
    "contraction",
    "connective_def",
    "ite_simplify",
    "eq_simplify",
    "and_simplify",
    "or_simplify",
    "not_simplify",
    "implies_simplify",
    "equiv_simplify",
    "bool_simplify",
    "qnt_simplify",
    "div_simplify",
    "prod_simplify",
    "unary_minus_simplify",
    "minus_simplify",
    "sum_simplify",
    "comp_simplify",
    "nary_elim",
    "ac_simp",
    "aci_simp",
    "bfun_elim",
    "bind",
    "qnt_cnf",
    "miniscope_distribute",
    "miniscope_split",
    "miniscope_ite",
    "subproof",
    "let",
    "onepoint",
    "sko_ex",
    "sko_forall",
    "reordering",
    "shuffle",
    "symm",
    "not_symm",
    "eq_symmetric",
    "eq_mp",
    "weakening",
    "bind_let",
    "la_mult_pos",
    "la_mult_neg",
    "la_mult_sign",
    "la_mult_abs_comparison",
    "mod_simplify",
    "evaluate",
    "beta_equiv",
    "div_intro",
    "log2_intro",
    "to_int_intro",
    "bitblast_const",
    "bitblast_var",
    "bitblast_and",
    "bitblast_or",
    "bitblast_xor",
    "bitblast_xnor",
    "bitblast_not",
    "bitblast_comp",
    "bitblast_ult",
    "bitblast_slt",
    "bitblast_add",
    "bitblast_mult",
    "bitblast_neg",
    "bitblast_equal",
    "bitblast_extract",
    "bitblast_concat",
    "bitblast_sign_extend",
    "bitblast_shl",
    "bitblast_lshr",
    "bitblast_ashr",
    "bitblast_udiv",
    "bitblast_urem",
    "arrays_idx",
    "arrays_row",
    "arrays_row_contra",
    "arrays_ext",
    "concat_eq",
    "concat_unify",
    "concat_conflict",
    "concat_csplit_prefix",
    "concat_csplit_suffix",
    "concat_split_prefix",
    "concat_split_suffix",
    "concat_lprop_prefix",
    "concat_lprop_suffix",
    "concat_cprop_prefix",
    "concat_cprop_suffix",
    "pbblast_bveq",
    "pbblast_bvult",
    "pbblast_bvugt",
    "pbblast_bvuge",
    "pbblast_bvule",
    "pbblast_bvslt",
    "pbblast_bvsgt",
    "pbblast_bvsge",
    "pbblast_bvsle",
    "pbblast_pbbvar",
    "pbblast_pbbconst",
    "pbblast_bvxor",
    "pbblast_bvand",
    "pbblast_bvxor_ith_bit",
    "pbblast_bvand_ith_bit",
    "cp_addition",
    "cp_multiplication",
    "cp_division",
    "cp_saturation",
    "cp_literal",
    "cp_normalize",
    "string_decompose",
    "string_length_pos",
    "string_length_non_empty",
    "re_inter",
    "re_kleene_star_unfold_pos",
    "re_concat_unfold_pos",
    "re_unfold_neg",
    "re_unfold_neg_concat_fixed_prefix",
    "re_unfold_neg_concat_fixed_suffix",
    "drup",
    "drat",
    "strict_resolution",
    "dt_project",
    "rare_rewrite",
    "sat_refutation",
];

type Path = Vec<usize>;

fn get<'a>(roots: &'a [Sx], path: &[usize]) -> Option<&'a Sx> {
    let mut cur = roots.get(path[0])?;
    for &i in &path[1..] {
        match cur {
            Sx::List(items) => cur = items.get(i)?,
            Sx::Atom(_) => return None,
        }
    }
    Some(cur)
}

fn get_mut<'a>(roots: &'a mut [Sx], path: &[usize]) -> Option<&'a mut Sx> {
    let mut cur = roots.get_mut(path[0])?;
    for &i in &path[1..] {
        match cur {
            Sx::List(items) => cur = items.get_mut(i)?,
            Sx::Atom(_) => return None,
        }
    }
    Some(cur)
}

/// Paths of every node inside a term position of the proof.
fn term_paths(proof: &[Sx]) -> (Vec<Path>, Vec<Path>) {
    let mut terms = Vec::new();
    let mut clause_lists = Vec::new();
    fn descend(node: &Sx, path: &mut Path, acc: &mut Vec<Path>) {
        acc.push(path.clone());
        if let Sx::List(items) = node {
            for (i, it) in items.iter().enumerate() {
                path.push(i);
                descend(it, path, acc);
                path.pop();
            }
        }
    }
    fn command(cmd: &Sx, path: &mut Path, terms: &mut Vec<Path>, clauses: &mut Vec<Path>) {
        let Sx::List(items) = cmd else { return };
        match items.first().and_then(Sx::as_atom) {
            Some("assume") => {
                if items.len() > 2 {
                    path.push(2);
                    descend(&items[2], path, terms);
                    path.pop();
                }
            }
            Some("step") | Some("anchor") => {
                for (i, it) in items.iter().enumerate() {
                    if i >= 2 {
                        if let Some("cl") = it.head() {
                            path.push(i);
                            clauses.push(path.clone());
                            if let Sx::List(lits) = it {
                                for (k, lit) in lits.iter().enumerate().skip(1) {
                                    path.push(k);
                                    descend(lit, path, terms);
                                    path.pop();
                                }
                            }
                            path.pop();
                        }
                    }
                    if i > 0 && matches!(items[i - 1].as_atom(), Some(":args")) {
                        path.push(i);
                        if let Sx::List(args) = it {
                            for (k, a) in args.iter().enumerate() {
                                path.push(k);
                                descend(a, path, terms);
                                path.pop();
                            }
                        }
                        path.pop();
                    }
                }
            }
            Some("define-fun") => {
                if let Some(body) = items.last() {
                    path.push(items.len() - 1);
                    descend(body, path, terms);
                    path.pop();
                }
            }
            _ => {}
        }
    }
    for (i, cmd) in proof.iter().enumerate() {
        let mut path = vec![i];
        command(cmd, &mut path, &mut terms, &mut clause_lists);
    }
    (terms, clause_lists)
}

fn atoms_of(roots: &[Sx], acc: &mut Vec<String>) {
    for r in roots {
        match r {
            Sx::Atom(a) => {
                if !a.starts_with(':') && a.len() < 40 {
                    acc.push(a.clone());
                }
            }
            Sx::List(items) => atoms_of(items, acc),
        }
    }
}

fn tweak_number(a: &str, rng: &mut Rng) -> Option<String> {
    if !a.is_empty() && a.chars().all(|c| c.is_ascii_digit()) {
        let n: i128 = a.parse().ok()?;
        let m = match rng.below(5) {
            0 => n + 1,
            1 => (n - 1).max(0),
            2 => n * 2,
            3 => 0,
            _ => n + 2,
        };
        return Some(m.to_string());
    }
    if let Some((i, f)) = a.split_once('.') {
        if i.chars().all(|c| c.is_ascii_digit())
            && f.chars().all(|c| c.is_ascii_digit())
            && !i.is_empty()
        {
            return Some(match rng.below(3) {
                0 => format!("{}.5", i),
                1 => format!("{}.0", i.parse::<u64>().ok()? + 1),
                _ => "0.0".to_owned(),
            });
        }
    }
    if let Some(bits) = a.strip_prefix("#b") {
        if !bits.is_empty() && bits.chars().all(|c| c == '0' || c == '1') {
            let mut b: Vec<char> = bits.chars().collect();
            match rng.below(4) {
                0 | 1 => {
                    let k = rng.below(b.len());
                    b[k] = if b[k] == '0' { '1' } else { '0' };
                }
                2 => b.insert(0, if rng.chance(50) { '1' } else { '0' }),
                _ => {
                    if b.len() > 1 {
                        b.remove(0);
                    }
                }
            }
            return Some(format!("#b{}", b.iter().collect::<String>()));
        }
    }
    None
}

fn random_path<'a>(paths: &'a [Path], rng: &mut Rng) -> Option<&'a Path> {
    rng.pick(paths)
}

/// Apply 1..=`max_rounds` random mutations. Returns `None` if nothing changed.
pub fn mutate(
    inst: &Instance,
    rng: &mut Rng,
    max_rounds: usize,
    allow_rule_swap: bool,
) -> Option<Instance> {
    let mut defs = sexp::parse(&inst.defs)?;
    let mut proof = sexp::parse(&inst.proof)?;
    let rounds = 1 + rng.below(max_rounds.max(1));
    let mut changed = false;
    for _ in 0..rounds {
        let (terms, clauses) = term_paths(&proof);
        let mut atoms = Vec::new();
        atoms_of(&proof, &mut atoms);
        atoms_of(&defs, &mut atoms);
        let kind = rng.below(if allow_rule_swap { 16 } else { 15 });
        match kind {
            // Replace a term node by another term node of the instance.
            0 | 1 => {
                let (Some(a), Some(b)) = (random_path(&terms, rng), random_path(&terms, rng))
                else {
                    continue;
                };
                let Some(src) = get(&proof, b).cloned() else {
                    continue;
                };
                if let Some(dst) = get_mut(&mut proof, a) {
                    *dst = src;
                    changed = true;
                }
            }
            // Replace a term node by an atom.
            2 => {
                let Some(a) = random_path(&terms, rng) else {
                    continue;
                };
                let atom = if rng.chance(60) {
                    rng.pick(&atoms).cloned()
                } else {
                    rng.pick(EXTRA_ATOMS).map(|s| s.to_string())
                };
                let Some(atom) = atom else { continue };
                let Some(parsed) = sexp::parse(&atom).and_then(|v| v.into_iter().next()) else {
                    continue;
                };
                if let Some(dst) = get_mut(&mut proof, a) {
                    *dst = parsed;
                    changed = true;
                }
            }
            // Swap an operator within its class.
            3 | 4 => {
                let candidates: Vec<&Path> = terms
                    .iter()
                    .filter(|p| {
                        get(&proof, p)
                            .and_then(Sx::as_atom)
                            .is_some_and(|a| OP_CLASSES.iter().any(|c| c.contains(&a)))
                    })
                    .collect();
                let Some(p) = rng.pick(&candidates).map(|p| (*p).clone()) else {
                    continue;
                };
                let Some(Sx::Atom(a)) = get(&proof, &p).cloned() else {
                    continue;
                };
                let classes: Vec<&&[&str]> = OP_CLASSES
                    .iter()
                    .filter(|c| c.contains(&a.as_str()))
                    .collect();
                let Some(class) = rng.pick(&classes) else {
                    continue;
                };
                let Some(new) = rng.pick(class) else { continue };
                if let Some(dst) = get_mut(&mut proof, &p) {
                    *dst = Sx::atom(new);
                    changed = true;
                }
            }
            // Duplicate, drop or swap arguments of an application.
            5 | 6 => {
                let lists: Vec<&Path> = terms
                    .iter()
                    .filter(|p| matches!(get(&proof, p), Some(Sx::List(items)) if items.len() >= 2))
                    .collect();
                let Some(p) = rng.pick(&lists).map(|p| (*p).clone()) else {
                    continue;
                };
                if let Some(Sx::List(items)) = get_mut(&mut proof, &p) {
                    let n = items.len();
                    match rng.below(3) {
                        0 => {
                            let k = 1 + rng.below(n - 1);
                            let copy = items[k].clone();
                            items.insert(k, copy);
                        }
                        1 if n > 2 => {
                            let k = 1 + rng.below(n - 1);
                            items.remove(k);
                        }
                        _ if n > 2 => {
                            let (i, j) = (1 + rng.below(n - 1), 1 + rng.below(n - 1));
                            items.swap(i, j);
                        }
                        _ => continue,
                    }
                    changed = true;
                }
            }
            // Perturb a numeral, decimal or bit-vector literal anywhere in the proof.
            7 | 8 => {
                let nums: Vec<&Path> = terms
                    .iter()
                    .filter(|p| {
                        get(&proof, p).and_then(Sx::as_atom).is_some_and(|a| {
                            a.starts_with("#b")
                                || a.chars().next().is_some_and(|c| c.is_ascii_digit())
                        })
                    })
                    .collect();
                let Some(p) = rng.pick(&nums).map(|p| (*p).clone()) else {
                    continue;
                };
                let Some(Sx::Atom(a)) = get(&proof, &p).cloned() else {
                    continue;
                };
                let Some(new) = tweak_number(&a, rng) else {
                    continue;
                };
                if let Some(dst) = get_mut(&mut proof, &p) {
                    *dst = Sx::Atom(new);
                    changed = true;
                }
            }
            // Wrap or unwrap a node.
            9 => {
                let Some(p) = random_path(&terms, rng).cloned() else {
                    continue;
                };
                let Some(node) = get(&proof, &p).cloned() else {
                    continue;
                };
                let new = if rng.chance(50) {
                    let w = rng.pick(&["not", "-", "bvneg", "bvnot", "abs"]).unwrap();
                    Sx::List(vec![Sx::atom(w), node])
                } else if let Sx::List(items) = &node {
                    if items.len() < 2 {
                        continue;
                    }
                    items[1 + rng.below(items.len() - 1)].clone()
                } else {
                    continue;
                };
                if let Some(dst) = get_mut(&mut proof, &p) {
                    *dst = new;
                    changed = true;
                }
            }
            // Change a sort: Int <-> Real, or a bit-vector width, in the definitions or binders.
            10 => {
                let in_defs = rng.chance(60);
                let target = if in_defs { &mut defs } else { &mut proof };
                changed |= tweak_sort(target, rng);
            }
            // Rename a binder variable, possibly into a clash with a free name.
            11 => {
                changed |= rename_binder(&mut proof, &atoms, rng);
            }
            // Clause edits: add, drop, swap, or negate literals.
            12 => {
                let Some(cp) = rng.pick(&clauses).cloned() else {
                    continue;
                };
                let other = random_path(&terms, rng).and_then(|p| get(&proof, p).cloned());
                if let Some(Sx::List(lits)) = get_mut(&mut proof, &cp) {
                    let n = lits.len();
                    match rng.below(4) {
                        0 => {
                            if let Some(o) = other {
                                lits.push(o);
                            }
                        }
                        1 if n > 1 => {
                            lits.remove(1 + rng.below(n - 1));
                        }
                        2 if n > 2 => {
                            let (i, j) = (1 + rng.below(n - 1), 1 + rng.below(n - 1));
                            lits.swap(i, j);
                        }
                        _ if n > 1 => {
                            let k = 1 + rng.below(n - 1);
                            let lit = lits[k].clone();
                            lits[k] = match lit {
                                Sx::List(ref items)
                                    if items.first().and_then(Sx::as_atom) == Some("not")
                                        && items.len() == 2 =>
                                {
                                    items[1].clone()
                                }
                                other => Sx::List(vec![Sx::atom("not"), other]),
                            };
                        }
                        _ => continue,
                    }
                    changed = true;
                }
            }
            // Premises and arguments of a step.
            13 | 14 => {
                changed |= tweak_premises_or_args(&mut proof, rng);
            }
            // Swap the rule name.
            _ => {
                let steps: Vec<usize> = proof
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| c.head() == Some("step"))
                    .map(|(i, _)| i)
                    .collect();
                let Some(&i) = rng.pick(&steps) else { continue };
                if let Sx::List(items) = &mut proof[i] {
                    if let Some(k) = items.iter().position(|x| x.as_atom() == Some(":rule")) {
                        if k + 1 < items.len() {
                            items[k + 1] = Sx::atom(rng.pick(RULES).unwrap());
                            changed = true;
                        }
                    }
                }
            }
        }
    }
    if !changed {
        return None;
    }
    Some(Instance {
        defs: sexp::print_all(&defs),
        proof: sexp::print_all(&proof),
    })
}

fn tweak_sort(roots: &mut [Sx], rng: &mut Rng) -> bool {
    let mut paths = Vec::new();
    fn find(node: &Sx, path: &mut Path, acc: &mut Vec<Path>) {
        match node {
            Sx::Atom(a) if a == "Int" || a == "Real" => acc.push(path.clone()),
            Sx::List(items) => {
                if items.len() == 3
                    && items[0].as_atom() == Some("_")
                    && items[1].as_atom() == Some("BitVec")
                {
                    acc.push(path.clone());
                    return;
                }
                for (i, it) in items.iter().enumerate() {
                    path.push(i);
                    find(it, path, acc);
                    path.pop();
                }
            }
            _ => {}
        }
    }
    for (i, r) in roots.iter().enumerate() {
        let mut path = vec![i];
        find(r, &mut path, &mut paths);
    }
    let Some(p) = rng.pick(&paths).cloned() else {
        return false;
    };
    let Some(node) = get_mut(roots, &p) else {
        return false;
    };
    match node {
        Sx::Atom(a) => {
            *a = if a == "Int" {
                "Real".into()
            } else {
                "Int".into()
            };
        }
        Sx::List(items) => {
            let w: usize = items[2].as_atom().and_then(|w| w.parse().ok()).unwrap_or(4);
            let nw = if rng.chance(50) {
                w + 1
            } else {
                w.saturating_sub(1).max(1)
            };
            items[2] = Sx::Atom(nw.to_string());
        }
    }
    true
}

fn rename_binder(proof: &mut [Sx], atoms: &[String], rng: &mut Rng) -> bool {
    let mut binders = Vec::new();
    fn find(node: &Sx, path: &mut Path, acc: &mut Vec<Path>) {
        if let Sx::List(items) = node {
            if matches!(
                items.first().and_then(Sx::as_atom),
                Some("forall" | "exists" | "lambda" | "choice")
            ) && items.len() == 3
            {
                acc.push(path.clone());
            }
            for (i, it) in items.iter().enumerate() {
                path.push(i);
                find(it, path, acc);
                path.pop();
            }
        }
    }
    for (i, r) in proof.iter().enumerate() {
        let mut path = vec![i];
        find(r, &mut path, &mut binders);
    }
    let Some(p) = rng.pick(&binders).cloned() else {
        return false;
    };
    let names: Vec<&String> = atoms
        .iter()
        .filter(|a| a.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) && !a.contains('.'))
        .collect();
    let Some(new) = rng.pick(&names).map(|s| (*s).clone()) else {
        return false;
    };
    let Some(Sx::List(items)) = get_mut(proof, &p) else {
        return false;
    };
    let Sx::List(bindings) = &mut items[1] else {
        return false;
    };
    if bindings.is_empty() {
        return false;
    }
    let k = rng.below(bindings.len());
    let Sx::List(binding) = &mut bindings[k] else {
        return false;
    };
    let Some(Sx::Atom(old)) = binding.first().cloned() else {
        return false;
    };
    binding[0] = Sx::Atom(new.clone());
    if rng.chance(50) {
        rename_free(&mut items[2], &old, &new);
    }
    true
}

fn rename_free(node: &mut Sx, old: &str, new: &str) {
    match node {
        Sx::Atom(a) if a == old => *a = new.to_owned(),
        Sx::List(items) => {
            for it in items {
                rename_free(it, old, new);
            }
        }
        _ => {}
    }
}

fn tweak_premises_or_args(proof: &mut [Sx], rng: &mut Rng) -> bool {
    let ids: Vec<String> = proof
        .iter()
        .filter_map(|c| match c {
            Sx::List(items)
                if matches!(items.first().and_then(Sx::as_atom), Some("step" | "assume")) =>
            {
                items.get(1).and_then(Sx::as_atom).map(str::to_owned)
            }
            _ => None,
        })
        .collect();
    let steps: Vec<usize> = proof
        .iter()
        .enumerate()
        .filter(|(_, c)| c.head() == Some("step"))
        .map(|(i, _)| i)
        .collect();
    let Some(&i) = rng.pick(&steps) else {
        return false;
    };
    let Sx::List(items) = &mut proof[i] else {
        return false;
    };
    let key = if rng.chance(50) { ":premises" } else { ":args" };
    let Some(k) = items.iter().position(|x| x.as_atom() == Some(key)) else {
        if key == ":premises" {
            if let Some(id) = rng.pick(&ids) {
                items.push(Sx::atom(":premises"));
                items.push(Sx::List(vec![Sx::Atom(id.clone())]));
                return true;
            }
        }
        return false;
    };
    let Some(Sx::List(list)) = items.get_mut(k + 1) else {
        return false;
    };
    let n = list.len();
    match rng.below(4) {
        0 if n > 0 => {
            list.remove(rng.below(n));
        }
        1 if n > 1 => {
            let (a, b) = (rng.below(n), rng.below(n));
            list.swap(a, b);
        }
        2 if key == ":premises" => {
            if let Some(id) = rng.pick(&ids) {
                if n > 0 {
                    let j = rng.below(n);
                    list[j] = Sx::Atom(id.clone());
                } else {
                    list.push(Sx::Atom(id.clone()));
                }
            }
        }
        _ if n > 0 => {
            let j = rng.below(n);
            if let Sx::Atom(a) = &list[j] {
                if let Some(t) = tweak_number(a, rng) {
                    list[j] = Sx::Atom(t);
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
        _ => return false,
    }
    true
}
