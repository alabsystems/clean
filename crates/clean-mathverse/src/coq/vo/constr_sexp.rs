// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Serializer from decoded [`Constr`] to importer-form sexps.
//!
//! The output follows serlib's (SerAPI 8.20) sexp shapes for `Constr.t`, so
//! `.vo`-decoded terms can be compared against — and eventually substituted
//! for — the `sertop`-produced dumps under `data/corpora/coq-sexp/`.
//!
//! Known divergence, by design: serlib 8.20 pierces `Univ.Level.UGlobal.t`
//! with a stale 2-field layout `(DirPath.t * int)` while the kernel stores
//! `{library; process; uid}`; the "int" serlib prints is actually the
//! `process` *string pointer* (nondeterministic garbage). We print the true
//! `uid` in that position. Comparisons must therefore normalize universe
//! level payloads (the `(Sort (Type _))` shape itself is stable).

use super::constr::{
    Binder, CaseData, CastKind, Constr, CtorRef, DirPath, IndRef, Instance, KerName, KerPair,
    Level, ModPath, QVar, Quality, RawLevel, RecDecl, Relevance, Sort,
};

/// Render one declaration in importer form:
/// `(CoqConstant <qualified-name> <type> <body>)`.
#[must_use]
pub fn coq_constant_sexp(qualified: &str, typ: &Constr, body: Option<&Constr>) -> String {
    let mut s = String::with_capacity(256);
    s.push_str("(CoqConstant ");
    s.push_str(qualified);
    s.push(' ');
    constr(&mut s, typ);
    if let Some(b) = body {
        s.push(' ');
        constr(&mut s, b);
    }
    s.push(')');
    s
}

/// Render a term as a SerAPI-shaped sexp string.
#[must_use]
pub fn constr_sexp(c: &Constr) -> String {
    let mut s = String::with_capacity(128);
    constr(&mut s, c);
    s
}

fn constr(s: &mut String, c: &Constr) {
    match c {
        Constr::Rel(i) => {
            s.push_str("(Rel ");
            push_i64(s, *i);
            s.push(')');
        }
        Constr::Var(id) => {
            s.push_str("(Var (Id ");
            s.push_str(id);
            s.push_str("))");
        }
        Constr::Sort(so) => {
            s.push_str("(Sort ");
            sort(s, so);
            s.push(')');
        }
        Constr::Cast(c1, k, t) => {
            s.push_str("(Cast ");
            constr(s, c1);
            s.push(' ');
            s.push_str(match k {
                CastKind::Vm => "VMcast",
                CastKind::Native => "NATIVEcast",
                CastKind::Default => "DEFAULTcast",
            });
            s.push(' ');
            constr(s, t);
            s.push(')');
        }
        Constr::Prod(b, t1, t2) => binder_node(s, "Prod", b, &[t1, t2]),
        Constr::Lambda(b, t, body) => binder_node(s, "Lambda", b, &[t, body]),
        Constr::LetIn(b, v, t, body) => binder_node(s, "LetIn", b, &[v, t, body]),
        Constr::App(head, args) => {
            s.push_str("(App ");
            constr(s, head);
            s.push_str(" (");
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                constr(s, a);
            }
            s.push_str("))");
        }
        Constr::Const(cu) => {
            let (kp, u) = cu.as_ref();
            s.push_str("(Const (");
            kerpair(s, "Constant", kp);
            s.push(' ');
            instance(s, u);
            s.push_str("))");
        }
        Constr::Ind(iu) => {
            let (ind, u) = iu.as_ref();
            s.push_str("(Ind (");
            ind_ref(s, ind);
            s.push(' ');
            instance(s, u);
            s.push_str("))");
        }
        Constr::Construct(cu) => {
            let (ctor, u) = cu.as_ref();
            s.push_str("(Construct (");
            ctor_ref(s, ctor);
            s.push(' ');
            instance(s, u);
            s.push_str("))");
        }
        Constr::Case(cd) => case(s, cd),
        Constr::Fix {
            struct_args,
            which,
            decl,
        } => {
            s.push_str("(Fix (((");
            for (i, a) in struct_args.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                push_i64(s, *a);
            }
            s.push_str(") ");
            push_i64(s, *which);
            s.push_str(") ");
            rec_decl(s, decl);
            s.push_str("))");
        }
        Constr::CoFix { which, decl } => {
            s.push_str("(CoFix (");
            push_i64(s, *which);
            s.push(' ');
            rec_decl(s, decl);
            s.push_str("))");
        }
        Constr::Proj(p, r, c1) => {
            s.push_str("(Proj (((proj_ind ");
            ind_ref(s, &p.ind);
            s.push_str(") (proj_npars ");
            push_i64(s, p.npars);
            s.push_str(") (proj_arg ");
            push_i64(s, p.arg);
            s.push_str(") (proj_name ");
            kerpair(s, "Constant", &p.name);
            s.push_str(")) ");
            s.push_str(if p.unfolded { "true" } else { "false" });
            s.push_str(") ");
            relevance(s, r);
            s.push(' ');
            constr(s, c1);
            s.push(')');
        }
        Constr::Uint63(i) => {
            s.push_str("(Int ");
            push_i64(s, *i);
            s.push(')');
        }
        Constr::Float64(f) => {
            s.push_str("(Float ");
            s.push_str(&format!("{f}"));
            s.push(')');
        }
        Constr::PStr(bytes) => {
            s.push_str("(String \"");
            s.push_str(&String::from_utf8_lossy(bytes));
            s.push_str("\")");
        }
        Constr::Array(payload) => {
            let (u, elems, def, ty) = payload.as_ref();
            s.push_str("(Array ");
            instance(s, u);
            s.push_str(" (");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                constr(s, e);
            }
            s.push_str(") ");
            constr(s, def);
            s.push(' ');
            constr(s, ty);
            s.push(')');
        }
    }
}

fn binder_node(s: &mut String, head: &str, b: &Binder, parts: &[&Constr]) {
    s.push('(');
    s.push_str(head);
    s.push(' ');
    binder(s, b);
    for p in parts {
        s.push(' ');
        constr(s, p);
    }
    s.push(')');
}

fn binder(s: &mut String, b: &Binder) {
    s.push_str("((binder_name ");
    match &b.name {
        None => s.push_str("Anonymous"),
        Some(n) => {
            s.push_str("(Name (Id ");
            s.push_str(n);
            s.push_str("))");
        }
    }
    s.push_str(") (binder_relevance ");
    relevance(s, &b.relevance);
    s.push_str("))");
}

fn relevance(s: &mut String, r: &Relevance) {
    match r {
        Relevance::Relevant => s.push_str("Relevant"),
        Relevance::Irrelevant => s.push_str("Irrelevant"),
        Relevance::Var(q) => {
            s.push_str("(RelevanceVar ");
            qvar(s, q);
            s.push(')');
        }
    }
}

fn qvar(s: &mut String, q: &QVar) {
    match q {
        QVar::Idx(i) => {
            s.push_str("(Var ");
            push_i64(s, *i);
            s.push(')');
        }
        QVar::Named(n, i) => {
            s.push_str("(Unif ");
            s.push_str(n);
            s.push(' ');
            push_i64(s, *i);
            s.push(')');
        }
    }
}

fn sort(s: &mut String, so: &Sort) {
    match so {
        Sort::SProp => s.push_str("SProp"),
        Sort::Prop => s.push_str("Prop"),
        Sort::Set => s.push_str("Set"),
        Sort::Type(u) => {
            s.push_str("(Type ");
            universe(s, u);
            s.push(')');
        }
        Sort::QSort(q, u) => {
            s.push_str("(QSort ");
            qvar(s, q);
            s.push(' ');
            universe(s, u);
            s.push(')');
        }
    }
}

fn universe(s: &mut String, u: &[(Level, i64)]) {
    s.push('(');
    for (i, (l, n)) in u.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        s.push('(');
        level(s, l);
        s.push(' ');
        push_i64(s, *n);
        s.push(')');
    }
    s.push(')');
}

fn level(s: &mut String, l: &Level) {
    s.push_str("((hash ");
    push_i64(s, l.hash);
    s.push_str(") (data ");
    match &l.data {
        RawLevel::Set => s.push_str("Set"),
        RawLevel::Var(i) => {
            s.push_str("(Var ");
            push_i64(s, *i);
            s.push(')');
        }
        RawLevel::Level(g) => {
            // serlib prints (dp <process-pointer>); we print the true uid.
            s.push_str("(Level (");
            dirpath(s, &g.library);
            s.push(' ');
            push_i64(s, g.uid);
            s.push_str("))");
        }
    }
    s.push_str("))");
}

fn dirpath(s: &mut String, dp: &DirPath) {
    s.push_str("(DirPath (");
    for (i, id) in dp.0.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        s.push_str("(Id ");
        s.push_str(id);
        s.push(')');
    }
    s.push_str("))");
}

fn modpath(s: &mut String, mp: &ModPath) {
    match mp {
        ModPath::File(dp) => {
            s.push_str("(MPfile ");
            dirpath(s, dp);
            s.push(')');
        }
        ModPath::Bound { uid, id, dp } => {
            s.push_str("(MPbound (");
            push_i64(s, *uid);
            s.push_str(" (Id ");
            s.push_str(id);
            s.push_str(") ");
            dirpath(s, dp);
            s.push_str("))");
        }
        ModPath::Dot(inner, label) => {
            s.push_str("(MPdot ");
            modpath(s, inner);
            s.push_str(" (Id ");
            s.push_str(label);
            s.push_str("))");
        }
    }
}

fn kername(s: &mut String, kn: &KerName) {
    s.push_str("(KerName ");
    modpath(s, &kn.modpath);
    s.push_str(" (Id ");
    s.push_str(&kn.label);
    s.push_str("))");
}

fn kerpair(s: &mut String, head: &str, kp: &KerPair) {
    s.push('(');
    s.push_str(head);
    s.push(' ');
    kername(s, &kp.user);
    s.push(' ');
    match &kp.canonical {
        None => s.push_str("()"),
        Some(c) => {
            s.push('(');
            kername(s, c);
            s.push(')');
        }
    }
    s.push(')');
}

fn ind_ref(s: &mut String, ind: &IndRef) {
    s.push('(');
    kerpair(s, "MutInd", &ind.mind);
    s.push(' ');
    push_i64(s, ind.index);
    s.push(')');
}

fn ctor_ref(s: &mut String, ctor: &CtorRef) {
    s.push('(');
    ind_ref(s, &ctor.ind);
    s.push(' ');
    push_i64(s, ctor.index);
    s.push(')');
}

fn instance(s: &mut String, u: &Instance) {
    s.push_str("(Instance ((");
    for (i, q) in u.qualities.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        match q {
            Quality::Var(v) => {
                s.push_str("(QVar ");
                qvar(s, v);
                s.push(')');
            }
            Quality::Constant(c) => s.push_str(match c {
                0 => "QSProp",
                1 => "QProp",
                _ => "QType",
            }),
        }
    }
    s.push_str(") (");
    for (i, l) in u.levels.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        level(s, l);
    }
    s.push_str(")))");
}

fn case(s: &mut String, cd: &CaseData) {
    s.push_str("(Case ((ci_ind ");
    ind_ref(s, &cd.info.ind);
    s.push_str(") (ci_npar ");
    push_i64(s, cd.info.npar);
    s.push_str(") (ci_cstr_ndecls (");
    push_i64_list(s, &cd.info.cstr_ndecls);
    s.push_str(")) (ci_cstr_nargs (");
    push_i64_list(s, &cd.info.cstr_nargs);
    s.push_str(")) (ci_pp_info ((style ");
    s.push_str(match cd.info.style {
        0 => "LetStyle",
        1 => "IfStyle",
        2 => "LetPatternStyle",
        3 => "MatchStyle",
        _ => "RegularStyle",
    });
    s.push_str(")))) ");
    instance(s, &cd.instance);
    s.push_str(" (");
    for (i, p) in cd.params.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        constr(s, p);
    }
    s.push_str(") (((");
    for (i, b) in cd.ret.binders.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        binder(s, b);
    }
    s.push_str(") ");
    constr(s, &cd.ret.body);
    s.push_str(") ");
    relevance(s, &cd.ret.relevance);
    s.push_str(") ");
    match &cd.invert {
        None => s.push_str("NoInvert"),
        Some(indices) => {
            s.push_str("(CaseInvert (");
            for (i, c) in indices.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                constr(s, c);
            }
            s.push_str("))");
        }
    }
    s.push(' ');
    constr(s, &cd.scrutinee);
    s.push_str(" (");
    for (i, br) in cd.branches.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        s.push_str("((");
        for (j, b) in br.binders.iter().enumerate() {
            if j > 0 {
                s.push(' ');
            }
            binder(s, b);
        }
        s.push_str(") ");
        constr(s, &br.body);
        s.push(')');
    }
    s.push_str("))");
}

fn rec_decl(s: &mut String, decl: &RecDecl) {
    s.push_str("((");
    for (i, b) in decl.binders.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        binder(s, b);
    }
    s.push_str(") (");
    for (i, t) in decl.types.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        constr(s, t);
    }
    s.push_str(") (");
    for (i, b) in decl.bodies.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        constr(s, b);
    }
    s.push_str("))");
}

fn push_i64(s: &mut String, i: i64) {
    s.push_str(&i.to_string());
}

fn push_i64_list(s: &mut String, xs: &[i64]) {
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        push_i64(s, *x);
    }
}
