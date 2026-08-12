// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Emission helpers for the SerAPI corpus dump driver.
//!
//! - Kernel-name qualification: `KerName(MPfile(DirPath((Id Peano)(Id
//!   Init)(Id Coq))))(Id plus_n_O)` → `Coq.Init.Peano.plus_n_O` (DirPath
//!   segments reversed, `MPdot` appends its segment).
//! - `CoqMInd` payload parsing (packets, arities, constructor names).
//! - The three importer output forms (`CoqConstant`/`CoqAxiom`/
//!   `CoqInductive`) with RAW SerAPI Constr payloads.

use crate::sexp_io::sexp_to_string;
use clean_mathverse::coq::alpha::Sexp;

// ---------------------------------------------------------------------------
// Assoc-list navigation + kernel-name qualification
// ---------------------------------------------------------------------------

/// Look up `key` in a list of `(key value ...)` pairs, returning the value.
pub(crate) fn assoc<'a>(fields: &'a [Sexp], key: &str) -> Option<&'a Sexp> {
    fields.iter().find_map(|f| match f {
        Sexp::List(kv) if kv.len() >= 2 => match &kv[0] {
            Sexp::Atom(k) if k == key => Some(&kv[1]),
            _ => None,
        },
        _ => None,
    })
}

fn atom_of(s: &Sexp) -> Option<&str> {
    match s {
        Sexp::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

/// Extract the identifier from `(Id x)` or a bare atom.
fn id_of(s: &Sexp) -> Option<String> {
    match s {
        Sexp::Atom(a) => Some(a.clone()),
        Sexp::List(v) if v.len() == 2 => match (&v[0], &v[1]) {
            (Sexp::Atom(h), Sexp::Atom(x)) if h == "Id" => Some(x.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Find the first `(KerName ...)` node anywhere inside `s`.
pub(crate) fn find_kername(s: &Sexp) -> Option<&Sexp> {
    if let Sexp::List(items) = s {
        if matches!(items.first(), Some(Sexp::Atom(h)) if h == "KerName") {
            return Some(s);
        }
        return items.iter().find_map(find_kername);
    }
    None
}

/// `(KerName <modpath> (Id x))` → `"<qualified-modpath>.x"`.
pub(crate) fn kername_to_qualified(s: &Sexp) -> Option<String> {
    let Sexp::List(items) = s else {
        return None;
    };
    if items.len() < 3 || !matches!(&items[0], Sexp::Atom(h) if h == "KerName") {
        return None;
    }
    let mp = modpath_to_qualified(&items[1])?;
    let id = id_of(&items[2])?;
    Some(format!("{mp}.{id}"))
}

/// Qualify a SerAPI module path: `MPfile(DirPath(segs))` reverses the
/// segments; `MPdot(mp, lbl)` appends its label. `MPbound` (functor
/// arguments) has no stable global name and yields `None`.
fn modpath_to_qualified(s: &Sexp) -> Option<String> {
    let Sexp::List(items) = s else {
        return None;
    };
    match atom_of(items.first()?)? {
        "MPfile" => {
            let Sexp::List(dp) = items.get(1)? else {
                return None;
            };
            if !matches!(dp.first(), Some(Sexp::Atom(h)) if h == "DirPath") {
                return None;
            }
            let Sexp::List(segs) = dp.get(1)? else {
                return None;
            };
            let mut parts: Vec<String> = segs.iter().map(id_of).collect::<Option<Vec<_>>>()?;
            parts.reverse();
            Some(parts.join("."))
        }
        "MPdot" => {
            let base = modpath_to_qualified(items.get(1)?)?;
            let lbl = id_of(items.get(2)?)?;
            Some(format!("{base}.{lbl}"))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// CoqMInd payload parsing
// ---------------------------------------------------------------------------

/// One inductive block of a mutual inductive.
pub(crate) struct MindPacket {
    pub typename: String,
    /// Full arity (params included) as a raw SerAPI Constr sexp plus whether
    /// a `TemplateArity` conclusion was collapsed to the shared single-level
    /// `Type` model (`template_collapsed` in the sidecar) — or the reason the
    /// arity could not be reconstructed.
    pub arity: Result<(Sexp, bool), String>,
    pub consnames: Vec<String>,
    /// `mind_user_lc` constructor types (fallback when `TypeOf` is empty).
    pub user_lc: Vec<Sexp>,
    /// The RAW `mind_user_arity` (unreduced) for a `RegularArity` packet, kept
    /// so a family whose constructors conclude through a definitional
    /// abbreviation (see [`ctor_conclusion_has_inductive_head`]) can fall back
    /// to it rather than the reduced arity `packet_arity` returns. `None` for
    /// `TemplateArity`.
    pub user_arity: Option<Sexp>,
}

/// Parsed summary of a `CoqMInd` answer payload.
pub(crate) struct MindInfo {
    /// Qualified name of the mutual block's kernel name (what `(Ind ...)`
    /// references in terms resolve against).
    pub base: Option<String>,
    pub nparams: u32,
    pub ntypes: u32,
    /// `Finite` | `CoFinite` | `BiFinite`.
    pub finite: String,
    pub prim_record: bool,
    pub packets: Vec<MindPacket>,
}

fn parse_u32(s: Option<&Sexp>) -> Option<u32> {
    s.and_then(atom_of).and_then(|a| a.parse().ok())
}

/// Parse the objects of a `(CoqMInd <mutind> <mind-body>)` answer (everything
/// after the `CoqMInd` head).
pub(crate) fn parse_mind(objs: &[Sexp]) -> Result<MindInfo, String> {
    let base = objs
        .first()
        .and_then(find_kername)
        .and_then(kername_to_qualified);
    let Some(Sexp::List(body)) = objs.get(1) else {
        return Err("CoqMInd: missing body".to_string());
    };
    let nparams = parse_u32(assoc(body, "mind_nparams")).ok_or("CoqMInd: missing mind_nparams")?;
    let ntypes = parse_u32(assoc(body, "mind_ntypes")).ok_or("CoqMInd: missing mind_ntypes")?;
    let finite = assoc(body, "mind_finite")
        .and_then(atom_of)
        .ok_or("CoqMInd: missing mind_finite")?
        .to_string();
    let prim_record = matches!(
        assoc(body, "mind_record"),
        Some(Sexp::List(v)) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "PrimRecord")
    );
    let Some(Sexp::List(raw_packets)) = assoc(body, "mind_packets") else {
        return Err("CoqMInd: missing mind_packets".to_string());
    };
    let mut packets = Vec::with_capacity(raw_packets.len());
    for rp in raw_packets {
        let Sexp::List(pf) = rp else {
            return Err("CoqMInd: malformed packet".to_string());
        };
        let typename = assoc(pf, "mind_typename")
            .and_then(id_of)
            .ok_or("CoqMInd: packet missing mind_typename")?;
        let consnames = match assoc(pf, "mind_consnames") {
            Some(Sexp::List(cs)) => cs
                .iter()
                .map(id_of)
                .collect::<Option<Vec<_>>>()
                .ok_or("CoqMInd: malformed mind_consnames")?,
            _ => return Err("CoqMInd: packet missing mind_consnames".to_string()),
        };
        let user_lc = match assoc(pf, "mind_user_lc") {
            Some(Sexp::List(tys)) => tys.clone(),
            _ => Vec::new(),
        };
        let user_arity = assoc(pf, "mind_arity").and_then(|arity| {
            let Sexp::List(av) = arity else { return None };
            if av.first().and_then(atom_of) != Some("RegularArity") {
                return None;
            }
            let Some(Sexp::List(fields)) = av.get(1) else {
                return None;
            };
            assoc(fields, "mind_user_arity").cloned()
        });
        packets.push(MindPacket {
            typename,
            arity: packet_arity(pf),
            consnames,
            user_lc,
            user_arity,
        });
    }
    Ok(MindInfo {
        base,
        nparams,
        ntypes,
        finite,
        prim_record,
        packets,
    })
}

/// Reconstruct a packet's FULL arity (params included), matching what the
/// importer expects as the `CoqInductive` arity payload. The returned flag is
/// `true` when a `TemplateArity` conclusion was collapsed (see below).
///
/// - `RegularArity` carries `mind_user_arity`, already the full arity Constr.
/// - `TemplateArity` carries only `template_level` — a raw template universe
///   payload (an algebraic `max(Set, u, ...)` expression instantiated per
///   use-site, e.g. `list`/`prod` in Coq.Init.Datatypes). A fixed algebraic
///   level is meaningless to the importer's collapsed single-level `Type`
///   model (and is correctly rejected as out-of-model), so per the shared
///   template contract the conclusion is collapsed to a plain single-level
///   `Type` sort at emission and tagged `template_collapsed` in the sidecar.
///   The binders are re-wrapped from `mind_arity_ctxt` (innermost-first).
fn packet_arity(packet: &[Sexp]) -> Result<(Sexp, bool), String> {
    let arity = assoc(packet, "mind_arity").ok_or("packet missing mind_arity")?;
    let Sexp::List(av) = arity else {
        return Err("mind_arity not a list".to_string());
    };
    match av.first().and_then(atom_of) {
        Some("RegularArity") => {
            // Emit the REDUCED kernel-canonical arity (the params+indices
            // telescope from `mind_arity_ctxt`, ending in the `mind_sort`
            // sort) rather than the raw `mind_user_arity`. Coq presents some
            // arities through definitional abbreviations whose codomain is a
            // delta-redex, e.g. `Im ... : Ensemble V` (with
            // `Ensemble V := V -> Prop`), whose `mind_user_arity` ends in
            // `App(Const Ensemble, [V])` — not a syntactic `Sort`. Clean's
            // purely-syntactic `add_inductive` rejects that ("type former does
            // not end in a sort") and under-counts indices (the `v:V` hidden
            // inside `Ensemble V`). `mind_arity_ctxt` is Coq's already-reduced
            // params+indices telescope (innermost-first) and `mind_sort` its
            // final sort, so wrapping the two reconstructs `∀ ... (v:V), Prop`,
            // which ends in a sort with the correct index count. For arities
            // that already end in a syntactic sort — the common case (`and`,
            // `or`, `eq`, ...) — this is byte-identical to `mind_user_arity`.
            let Some(Sexp::List(fields)) = av.get(1) else {
                return Err("RegularArity: missing fields".to_string());
            };
            let ctxt = match assoc(packet, "mind_arity_ctxt") {
                Some(Sexp::List(c)) => c.as_slice(),
                _ => &[],
            };
            let sort = assoc(fields, "mind_sort").ok_or("RegularArity: missing mind_sort")?;
            let concl = Sexp::List(vec![Sexp::Atom("Sort".to_string()), sort.clone()]);
            wrap_arity_ctxt(ctxt, concl).map(|a| (a, false))
        }
        Some("TemplateArity") => {
            let ctxt = match assoc(packet, "mind_arity_ctxt") {
                Some(Sexp::List(c)) => c.as_slice(),
                _ => &[],
            };
            let concl = template_collapsed_sort(ctxt.is_empty());
            wrap_arity_ctxt(ctxt, concl).map(|a| (a, true))
        }
        other => Err(format!("unknown mind_arity head: {other:?}")),
    }
}

/// The collapsed single-level `Type` conclusion for a `TemplateArity`.
///
/// The shape is dialect-sensitive because the importer's SerAPI detection
/// keys on marker atoms (binder records / kernel-name wrappers):
/// - a PARAMETERIZED arity (non-empty `mind_arity_ctxt` wraps binder-record
///   `Prod`s around the conclusion) is normalized as SerAPI-native, so the
///   conclusion must be an in-model SerAPI universe — exactly one
///   `(<level-expr> 0)` pair with a named global `Level` datum, which the
///   importer collapses to its single `Type` level;
/// - a BARE conclusion (no binders anywhere, defensive: template polymorphism
///   requires parameters) passes through un-normalized, so it must already be
///   the importer-dialect `(Sort (Type 1))`.
fn template_collapsed_sort(bare: bool) -> Sexp {
    let atom = |s: &str| Sexp::Atom(s.to_string());
    if bare {
        return Sexp::List(vec![
            atom("Sort"),
            Sexp::List(vec![atom("Type"), atom("1")]),
        ]);
    }
    // ((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0))))
    let level_expr = Sexp::List(vec![
        Sexp::List(vec![atom("hash"), atom("0")]),
        Sexp::List(vec![
            atom("data"),
            Sexp::List(vec![
                atom("Level"),
                Sexp::List(vec![
                    Sexp::List(vec![
                        atom("DirPath"),
                        Sexp::List(vec![Sexp::List(vec![
                            atom("Id"),
                            atom("mathverse_template_collapse"),
                        ])]),
                    ]),
                    atom("0"),
                ]),
            ]),
        ]),
    ]);
    let pair = Sexp::List(vec![level_expr, atom("0")]);
    Sexp::List(vec![
        atom("Sort"),
        Sexp::List(vec![atom("Type"), Sexp::List(vec![pair])]),
    ])
}

/// Wrap a conclusion sort in the binders of `mind_arity_ctxt` (innermost
/// binder listed first, so wrapping in list order builds outward).
fn wrap_arity_ctxt(ctxt: &[Sexp], concl: Sexp) -> Result<Sexp, String> {
    let mut acc = concl;
    for decl in ctxt {
        let Sexp::List(dv) = decl else {
            return Err("arity ctxt: malformed decl".to_string());
        };
        match dv.first().and_then(atom_of) {
            Some("LocalAssum") if dv.len() >= 3 => {
                acc = Sexp::List(vec![
                    Sexp::Atom("Prod".to_string()),
                    dv[1].clone(),
                    dv[2].clone(),
                    acc,
                ]);
            }
            Some("LocalDef") if dv.len() >= 4 => {
                acc = Sexp::List(vec![
                    Sexp::Atom("LetIn".to_string()),
                    dv[1].clone(),
                    dv[2].clone(),
                    dv[3].clone(),
                    acc,
                ]);
            }
            other => return Err(format!("arity ctxt: unknown decl head {other:?}")),
        }
    }
    Ok(acc)
}

/// True when a constructor's conclusion (the codomain reached after walking
/// its `Prod` telescope) has an INDUCTIVE head — `(Ind ...)` or
/// `(App (Ind ...) ...)`.
///
/// A `(Const ...)`/`(App (Const ...) ...)` head means the conclusion is written
/// through a definitional abbreviation, e.g. Coq's `Image.Im`:
///   `Im_intro : ... -> In V (Im U V X f) (f x)`   (`In A a := A a`)
/// whose syntactic conclusion head is the CONSTANT `In`, not the inductive `Im`.
/// The importer buckets constructors by that syntactic head, so a synonym-headed
/// conclusion sends `Im_intro` to `In` and leaves `Im` with zero constructors —
/// which, combined with a reduced (sort-ending) arity, would import `Im` as a
/// WRONG zero-constructor inductive and break its dependent lemmas. Families
/// with a synonym-headed constructor therefore keep their raw (unreduced) arity
/// so they stay axiomatized exactly as before, while families whose
/// constructors conclude directly in the inductive (`clos_refl_sym_trans`, …)
/// get the reduced arity and import correctly.
pub(crate) fn ctor_conclusion_has_inductive_head(ctor_ty: &Sexp) -> bool {
    let mut cur = ctor_ty;
    loop {
        match cur {
            Sexp::List(v) if v.first().and_then(atom_of) == Some("Prod") && v.len() >= 4 => {
                cur = &v[3];
            }
            Sexp::List(v) if v.first().and_then(atom_of) == Some("LetIn") && v.len() >= 5 => {
                cur = &v[4];
            }
            _ => break,
        }
    }
    let head = match cur {
        Sexp::List(v) if v.first().and_then(atom_of) == Some("App") => v.get(1),
        other => Some(other),
    };
    matches!(head, Some(Sexp::List(v)) if v.first().and_then(atom_of) == Some("Ind"))
}

// ---------------------------------------------------------------------------
// Output forms
// ---------------------------------------------------------------------------

/// `(CoqConstant "<name>" <type> <value>)` — one line, newline-terminated.
pub(crate) fn render_constant(name: &str, ty: &Sexp, value: &Sexp) -> String {
    let form = Sexp::List(vec![
        Sexp::Atom("CoqConstant".to_string()),
        Sexp::Atom(name.to_string()),
        ty.clone(),
        value.clone(),
    ]);
    let mut s = sexp_to_string(&form);
    s.push('\n');
    s
}

/// `(CoqConstant "<name>" <type> <value> Speculative)` — one line.
///
/// The INSTANTIATED-MODULE (functor-application) variant of
/// [`render_constant`]: an enumerated functor member (`PositiveMap.ME.eqk`,
/// `NatSort.merge`, …) is a fresh global kernel constant with a REAL
/// value-bearing body, but that body is functor-generated and the Clean kernel
/// may not delta/iota-reduce through the instantiation. The trailing
/// `Speculative` marker atom records IN the dump that the value is an
/// OPTIMISTIC emission: the importer profiles the row
/// `AxiomProfile::SPECULATIVE_MOTIVE`, so the verify side arbitrates it
/// fail-closed — the kernel ACCEPTS → genuine `KernelVerified`, REJECTS →
/// clean value-less type-only axiom (no masked-failure taint; it joins the
/// stand-in set so dependents that need the withheld value classify
/// STANDIN_BLOCKED rather than masked-tainted). The value PAYLOAD is
/// byte-identical to [`render_constant`]'s — the same `ty`/`value` sexps in
/// the same positions — only a 5th marker atom is appended, which every
/// min-arity `CoqConstant` reader ignores. Genuine `:= Struct` members must
/// keep using [`render_constant`]: their values are ordinary, not
/// functor-generated, and marking them speculative would needlessly withhold
/// them from KV under a masked-taint dependency.
pub(crate) fn render_constant_speculative(name: &str, ty: &Sexp, value: &Sexp) -> String {
    let form = Sexp::List(vec![
        Sexp::Atom("CoqConstant".to_string()),
        Sexp::Atom(name.to_string()),
        ty.clone(),
        value.clone(),
        Sexp::Atom("Speculative".to_string()),
    ]);
    let mut s = sexp_to_string(&form);
    s.push('\n');
    s
}

/// `(CoqAxiom "<name>" <type>)` — one line, newline-terminated.
pub(crate) fn render_axiom(name: &str, ty: &Sexp) -> String {
    let form = Sexp::List(vec![
        Sexp::Atom("CoqAxiom".to_string()),
        Sexp::Atom(name.to_string()),
        ty.clone(),
    ]);
    let mut s = sexp_to_string(&form);
    s.push('\n');
    s
}

/// `(CoqAxiom "<name>" <type> StandIn)` — one line, newline-terminated.
///
/// The CRASH-SALVAGE variant of [`render_axiom`]: the trailing `StandIn`
/// marker atom records IN the dump that this axiom stands in for a
/// declaration Coq's kernel checked a value/structure for (the payload
/// crashed sertop's serializer; only the statement survived). The importer
/// profiles such rows `AxiomProfile::SALVAGED_STAND_IN`, which the verify
/// side's stand-in-blocked rejection classification consumes. Backward
/// compatible: every consumer parses `CoqAxiom` forms with min-arity checks
/// and reads only the name/type, so the extra atom is ignored by older
/// readers. Genuine Coq `Axiom`/`Parameter` declarations must keep using
/// [`render_axiom`] — they are value-less in Coq too, so a conversion blocked
/// at them is NOT a reconstruction gap.
pub(crate) fn render_axiom_standin(name: &str, ty: &Sexp) -> String {
    let form = Sexp::List(vec![
        Sexp::Atom("CoqAxiom".to_string()),
        Sexp::Atom(name.to_string()),
        ty.clone(),
        Sexp::Atom("StandIn".to_string()),
    ]);
    let mut s = sexp_to_string(&form);
    s.push('\n');
    s
}

/// `(CoqInductive "<base>" <block> <arity> (NumParams k) (Ctor "<cname>"
/// <ctype>)...)` — one line, newline-terminated.
pub(crate) fn render_inductive(
    base: &str,
    block: u32,
    arity: &Sexp,
    nparams: u32,
    ctors: &[(String, Sexp)],
) -> String {
    let mut items = vec![
        Sexp::Atom("CoqInductive".to_string()),
        Sexp::Atom(base.to_string()),
        Sexp::Atom(block.to_string()),
        arity.clone(),
        Sexp::List(vec![
            Sexp::Atom("NumParams".to_string()),
            Sexp::Atom(nparams.to_string()),
        ]),
    ];
    for (cname, cty) in ctors {
        items.push(Sexp::List(vec![
            Sexp::Atom("Ctor".to_string()),
            Sexp::Atom(cname.clone()),
            cty.clone(),
        ]));
    }
    let mut s = sexp_to_string(&Sexp::List(items));
    s.push('\n');
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp_io::parse_sexp_utf8;

    #[test]
    fn test_render_constant_speculative_appends_marker_without_changing_value() {
        // The `Speculative` marker must be a PURE APPENDED atom: the type and
        // value payloads are byte-identical to `render_constant`, so the
        // importer parses exactly the same value (semantic fidelity — we mark
        // an existing value-bearing emission, never rewrite the value).
        let p = |s: &str| parse_sexp_utf8(s).expect("parse");
        let ty = p("(Prod ((binder_name Anonymous)) (Sort Prop) (Sort Prop))");
        let value = p("(Lambda ((binder_name (Name (Id x)))) (Sort Prop) (Rel 1))");
        let plain = render_constant("Foo.bar", &ty, &value);
        let spec = render_constant_speculative("Foo.bar", &ty, &value);
        // The speculative form is the plain form with the trailing `)` replaced
        // by ` Speculative)` — the CoqConstant head/name/type/value bytes are
        // otherwise identical.
        let plain_body = plain.trim_end().trim_end_matches(')');
        assert!(
            spec.trim_end().starts_with(plain_body),
            "speculative form must extend the plain form verbatim:\n plain={plain}\n spec ={spec}"
        );
        assert!(
            spec.trim_end().ends_with(" Speculative)"),
            "speculative form must end with the marker atom: {spec}"
        );
        // Re-parse both and confirm the value sub-sexp (index 3) is equal.
        let plain_sx = parse_sexp_utf8(plain.trim_end()).expect("plain parses");
        let spec_sx = parse_sexp_utf8(spec.trim_end()).expect("spec parses");
        let (Sexp::List(pv), Sexp::List(sv)) = (&plain_sx, &spec_sx) else {
            panic!("both render as lists")
        };
        assert_eq!(pv.len(), 4, "plain CoqConstant has 4 items");
        assert_eq!(sv.len(), 5, "speculative CoqConstant has 5 items (marker)");
        assert_eq!(pv[1], sv[1], "name unchanged");
        assert_eq!(pv[2], sv[2], "type unchanged");
        assert_eq!(pv[3], sv[3], "value unchanged by the marker");
        assert_eq!(sv[4], Sexp::Atom("Speculative".to_string()));
    }

    #[test]
    fn test_kername_to_qualified_reverses_dirpath() {
        let src = "(KerName(MPfile(DirPath((Id Peano)(Id Init)(Id Coq))))(Id plus_n_O))";
        let kn = parse_sexp_utf8(src).expect("should parse kername");
        assert_eq!(
            kername_to_qualified(&kn).as_deref(),
            Some("Coq.Init.Peano.plus_n_O")
        );
    }

    #[test]
    fn test_ctor_conclusion_head_inductive_vs_synonym() {
        let p = |s: &str| parse_sexp_utf8(s).expect("parse");
        // clos_refl_sym_trans-style: constructor concludes directly in the
        // inductive -> `(App (Ind ...) ...)` head -> reduce-safe.
        let ind_headed = p(
            "(Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 2) \
             (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id R)))) (Id foo)) ()) 0) \
             (Instance (() ())))) ((Rel 3) (Rel 1))))",
        );
        assert!(ctor_conclusion_has_inductive_head(&ind_headed));
        // Im_intro-style: constructor concludes through the `In` synonym ->
        // `(App (Const ...) ...)` head -> must keep the raw arity.
        let synonym_headed = p(
            "(Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 2) \
             (App (Const ((Constant (KerName (MPfile (DirPath ((Id Ensembles)))) (Id In)) ()) \
             (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1))))",
        );
        assert!(!ctor_conclusion_has_inductive_head(&synonym_headed));
        // A nullary conclusion that is a bare `(Ind ...)` (no `App`) counts too.
        let bare_ind = p(
            "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes)))) (Id nat)) ()) 0) \
             (Instance (() ()))))",
        );
        assert!(ctor_conclusion_has_inductive_head(&bare_ind));
    }

    #[test]
    fn test_kername_to_qualified_mpdot_appends_segment() {
        let src =
            "(KerName(MPdot(MPfile(DirPath((Id PeanoNat)(Id Arith)(Id Coq))))(Id Nat))(Id add))";
        let kn = parse_sexp_utf8(src).expect("should parse kername");
        assert_eq!(
            kername_to_qualified(&kn).as_deref(),
            Some("Coq.Arith.PeanoNat.Nat.add")
        );
    }

    #[test]
    fn test_parse_mind_regular_arity_nat_shape() {
        let src =
            "(CoqMInd(MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())\
            ((mind_packets(((mind_typename(Id nat))(mind_arity_ctxt())\
            (mind_arity(RegularArity((mind_user_arity(Sort Set))(mind_sort Set))))\
            (mind_consnames((Id O)(Id S)))(mind_user_lc()))))\
            (mind_finite Finite)(mind_ntypes 1)(mind_nparams 0)(mind_record NotRecord)))";
        let parsed = parse_sexp_utf8(src).expect("should parse mind fixture");
        let Sexp::List(items) = &parsed else {
            panic!("expected list");
        };
        let info = parse_mind(&items[1..]).expect("should extract mind info");
        assert_eq!(info.base.as_deref(), Some("Coq.Init.Datatypes.nat"));
        assert_eq!((info.nparams, info.ntypes), (0, 1));
        assert_eq!(info.finite, "Finite");
        assert!(!info.prim_record);
        assert_eq!(info.packets.len(), 1);
        let p = &info.packets[0];
        assert_eq!(p.typename, "nat");
        assert_eq!(p.consnames, vec!["O".to_string(), "S".to_string()]);
        let (arity, template) = p.arity.as_ref().expect("arity should reconstruct");
        assert_eq!(sexp_to_string(arity), "(Sort Set)");
        assert!(!template, "RegularArity is never template-collapsed");
    }

    #[test]
    fn test_packet_arity_template_collapses_to_single_level() {
        // list-like: one (A : Type) param in the arity ctxt; the raw
        // template_level (an algebraic max) is REPLACED by the collapsed
        // in-model single-level SerAPI universe.
        let src = "((mind_typename(Id list))\
            (mind_arity_ctxt((LocalAssum((binder_name(Name(Id A)))(binder_relevance Relevant))(Sort(Type U)))))\
            (mind_arity(TemplateArity((template_level(Type U))))))";
        let parsed = parse_sexp_utf8(src).expect("should parse packet fixture");
        let Sexp::List(pf) = &parsed else {
            panic!("expected list");
        };
        let (arity, template) = packet_arity(pf).expect("template arity should reconstruct");
        assert!(template, "TemplateArity must tag template_collapsed");
        assert_eq!(
            sexp_to_string(&arity),
            "(Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type U)) \
             (Sort (Type ((((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0)))) 0)))))"
        );
    }

    #[test]
    fn test_packet_arity_template_bare_ctxt_uses_importer_dialect() {
        // Defensive: a template arity with an empty binder context has no
        // SerAPI marker anywhere, so the conclusion must be the pass-through
        // importer-dialect form.
        let src = "((mind_typename(Id t))\
            (mind_arity_ctxt())\
            (mind_arity(TemplateArity((template_level(Type U))))))";
        let parsed = parse_sexp_utf8(src).expect("should parse packet fixture");
        let Sexp::List(pf) = &parsed else {
            panic!("expected list");
        };
        let (arity, template) = packet_arity(pf).expect("template arity should reconstruct");
        assert!(template);
        assert_eq!(sexp_to_string(&arity), "(Sort (Type 1))");
    }

    #[test]
    fn test_render_inductive_matches_importer_grammar() {
        let arity = parse_sexp_utf8("(Sort Set)").expect("arity");
        let cty = parse_sexp_utf8("(Ind nat 0)").expect("ctor type");
        let s = render_inductive(
            "Coq.Init.Datatypes.nat",
            0,
            &arity,
            0,
            &[("Coq.Init.Datatypes.O".to_string(), cty)],
        );
        assert_eq!(
            s,
            "(CoqInductive Coq.Init.Datatypes.nat 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.O (Ind nat 0)))\n"
        );
    }
}
