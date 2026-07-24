// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-content enumeration from `Print Module <M>.` output.
//!
//! sertop answers the Vernac query with a `Feedback` `Message` that carries
//! both a `Pp` tree and a plain `(str "...")` rendering. We use the plain
//! string: sentences are split on `'.'`-followed-by-whitespace (qualified
//! names like `Nat.pred` have no space after the dot, so they survive), and
//! each sentence's leading keyword + identifier yields a candidate name.
//!
//! Classification is NOT taken from the printed keyword — `Print Module`
//! shows Qed-opaque theorems as `Parameter` — the driver classifies every
//! candidate by live `Definition`/`TypeOf` queries. The keyword is recorded
//! only as a hint in the sidecar skip reasons.
//!
//! Nested modules are NOT expanded by `Print Module` (verified live on
//! `Coq.Arith.PeanoNat`: the inner `Module Nat` prints as a bodyless line).
//! Such lines are returned as `submodules` so the driver can recursively
//! `Print Module` them.

use crate::sexp_io::parse_sexp_utf8;
use clean_mathverse::coq::alpha::Sexp;

/// A candidate declaration discovered by enumeration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate {
    /// Fully-qualified name (module path + identifier).
    pub qualified: String,
    /// The keyword `Print Module` used (hint only, not a classification).
    pub keyword: String,
    /// Set when the member was enumerated from an INSTANTIATED-module root
    /// print (`Module M : Sig <members> End := (F X)`, a functor
    /// APPLICATION): the members are fresh, fully-qualified-queryable global
    /// kernel constants, but their VALUES are functor-generated
    /// reconstructions the Clean kernel may not reduce through. The driver
    /// still dumps such a member VALUE-BEARING (so the ~22 that verify KV
    /// stay KV), but tags the `(CoqConstant …)` with a trailing `Speculative`
    /// marker atom (see [`crate::emit::render_constant_speculative`]) so the
    /// importer profiles it `AxiomProfile::SPECULATIVE_MOTIVE`: the verify
    /// side arbitrates it fail-closed — kernel accepts → genuine KV, rejects
    /// → clean value-less type-only axiom (no masked-failure taint, joins the
    /// stand-in set). This is the Option-B re-land of the enumeration prong
    /// (the earlier bare-value-bearing enumeration measured −885 at corpus
    /// scale because rejected members entered as masked-failure taint seeds).
    /// A NON-instantiated (`:= Struct`) member keeps `false` and dumps
    /// value-bearing WITHOUT the marker, exactly as before.
    pub speculative: bool,
}

/// Result of parsing one `Print Module` listing.
#[derive(Debug, Default)]
pub struct Listing {
    pub candidates: Vec<Candidate>,
    /// Qualified paths of bodyless nested modules that need their own
    /// `Print Module` pass.
    pub submodules: Vec<String>,
    /// Qualified paths of FUNCTOR modules (`Module F := Functor (X:SIG) ...
    /// Struct ... End`): their members are functor-scoped (`MPbound`), not
    /// global kernel constants, so the body is suppressed and the driver
    /// records one counted skip per functor — never silent.
    pub functors: Vec<String>,
    /// Set when the ROOT print is an INSTANTIATED-module signature region
    /// (`Module M : Sig <members> End := <target>`, a module minted by a
    /// functor APPLICATION or reached by ALIAS — both print the resolved
    /// signature with NO syntactic `Struct` body). Every candidate discovered
    /// in such a listing is a fresh, fully-qualified-queryable global constant
    /// whose value is functor/alias-generated, so it is marked
    /// [`Candidate::speculative`] and the driver emits it VALUE-BEARING with
    /// the fail-closed `Speculative` marker (kernel accepts → KV, rejects →
    /// clean type-only, never masked taint).
    ///
    /// Opening the enumerating region here is a STRICT SUPERSET of main's
    /// behavior: without it the header sentence bails at `: Sig` after queuing
    /// a bogus `<path>.<path>` submodule, dropping the header-sentence member
    /// (`ME.eqk`) and never recursing into the nested modules (`ME.MO` + its
    /// tower). Later member sentences enumerate identically (same
    /// stack-empty-vs-region prefix = the module path), so no previously-dumped
    /// name is lost — the prong only recovers the dropped member and queues the
    /// real submodules for recursion.
    pub root_instantiated: bool,
}

/// Extract the concatenated Notice-message plain text from feedback lines.
///
/// NOTICE-ONLY: a query's answer text (`Print Module` listing, `Check` type,
/// `Print` body) is always a `(level Notice)` message; `Warning`/`Info`
/// messages emitted while the query runs are diagnostics, not payload.
/// Concatenating them used to SILENTLY corrupt module enumeration — measured
/// live on `mathcomp.algebra.rat`, where the `notation-overridden` warning's
/// tail token glued onto the dot-less `Module rat := Struct Record rat ...`
/// sentence, so `process_statement` bailed on the unknown token and the `rat`
/// inductive was dropped with no skip entry.
pub fn extract_message_str(feedback: &[String]) -> Option<String> {
    let mut acc = String::new();
    for line in feedback {
        // Cheap pre-filter: only Message feedback carries a (str ...) field.
        if !line.contains("(Message") {
            continue;
        }
        let Ok(sx) = parse_sexp_utf8(line) else {
            continue;
        };
        let Some(msg) = find_list_with_head(&sx, "Message") else {
            continue;
        };
        let Sexp::List(fields) = msg else {
            continue;
        };
        if !matches!(field_value(fields, "level"), Some(Sexp::Atom(l)) if l == "Notice") {
            continue;
        }
        if let Some(Sexp::Atom(text)) = field_value(fields, "str") {
            if !acc.is_empty() {
                acc.push('\n');
            }
            acc.push_str(text);
        }
    }
    if acc.is_empty() {
        None
    } else {
        Some(acc)
    }
}

fn find_list_with_head<'a>(s: &'a Sexp, head: &str) -> Option<&'a Sexp> {
    if let Sexp::List(items) = s {
        if matches!(items.first(), Some(Sexp::Atom(h)) if h == head) {
            return Some(s);
        }
        return items.iter().find_map(|c| find_list_with_head(c, head));
    }
    None
}

fn field_value<'a>(fields: &'a [Sexp], key: &str) -> Option<&'a Sexp> {
    fields.iter().find_map(|f| match f {
        Sexp::List(kv) if kv.len() >= 2 => match &kv[0] {
            Sexp::Atom(k) if k == key => Some(&kv[1]),
            _ => None,
        },
        _ => None,
    })
}

/// Keywords whose statement declares a constant-like candidate.
const CONSTANT_KEYWORDS: &[&str] = &[
    "Definition",
    "Parameter",
    "Parameters",
    "Axiom",
    "Axioms",
    "Theorem",
    "Lemma",
    "Fact",
    "Remark",
    "Corollary",
    "Fixpoint",
    "CoFixpoint",
    "Instance",
    "Primitive",
];

/// Keywords whose statement declares an inductive-block candidate.
const INDUCTIVE_KEYWORDS: &[&str] = &[
    "Inductive",
    "CoInductive",
    "Variant",
    "Record",
    "Structure",
    "Class",
];

/// Leading modifiers to strip before keyword matching.
const MODIFIERS: &[&str] = &[
    "Polymorphic",
    "Monomorphic",
    "Cumulative",
    "NonCumulative",
    "Private",
    "Program",
];

/// Parse the flattened `Print Module` listing into qualified candidates plus
/// bodyless nested modules (which need their own recursive `Print Module`).
///
/// Tracks inline `Module X := Struct ... End` prefixes; skips the bodies of
/// `Module Type`/`Sig` regions (their fields are specification parameters,
/// not global declarations).
pub fn parse_module_listing(text: &str, module: &str) -> Listing {
    let mut listing = Listing::default();
    // (prefix, is_sig) stack; the outermost Struct is the module itself.
    let mut stack: Vec<(String, bool)> = Vec::new();
    for sentence in split_sentences(text) {
        let tokens: Vec<&str> = sentence.split_whitespace().collect();
        process_statement(&tokens, module, &mut stack, &mut listing);
    }
    listing
}

/// Split on `'.'` followed by whitespace or end-of-input.
fn split_sentences(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let b = text.as_bytes();
    let mut start = 0usize;
    for i in 0..b.len() {
        if b[i] == b'.' && (i + 1 >= b.len() || b[i + 1].is_ascii_whitespace()) {
            out.push(&text[start..i]);
            start = i + 1;
        }
    }
    if start < text.len() {
        out.push(&text[start..]);
    }
    out
}

fn current_prefix(stack: &[(String, bool)], module: &str) -> String {
    stack
        .last()
        .map_or_else(|| module.to_string(), |(p, _)| p.clone())
}

fn in_sig(stack: &[(String, bool)]) -> bool {
    stack.last().is_some_and(|(_, s)| *s)
}

/// Consume one "statement" worth of tokens, iteratively.
///
/// Two real printed shapes must both work (verified live):
/// - FILE modules print full sentences with types
///   (`Definition not : Prop -> Prop.`) — after `<keyword> <name>` the next
///   token is not a keyword, which ends the chain for that sentence.
/// - INNER modules print a compact name-only listing with NO sentence dots
///   (`Definition t Definition zero ...` after whitespace flattening,
///   verified on `Coq.Arith.PeanoNat.Nat`) — the loop chains through every
///   `<keyword> <name>` pair in the single giant sentence.
fn process_statement(
    tokens: &[&str],
    module: &str,
    stack: &mut Vec<(String, bool)>,
    listing: &mut Listing,
) {
    let mut toks = tokens;
    loop {
        while let Some(first) = toks.first() {
            if MODIFIERS.contains(first) {
                toks = &toks[1..];
            } else {
                break;
            }
        }
        let Some(&kw) = toks.first() else {
            return;
        };
        match kw {
            "End" => {
                stack.pop();
                // `End` carries no sentence dot; the next declaration may
                // share the sentence ("... End Definition next : ...").
                toks = &toks[1..];
            }
            "Module" => {
                let (is_type, name_idx) = if toks.get(1) == Some(&"Type") {
                    (true, 2)
                } else {
                    (false, 1)
                };
                let Some(name) = toks.get(name_idx) else {
                    return;
                };
                let name = name.trim_end_matches([':', '=']);
                // Optional sealing ascription between the name and the body
                // (verified live: the sealed `Module RbaseSymbolsImpl :
                // RbaseSymbolsSig := Struct ... End` in Coq.Reals.Rdefinitions
                // prints its full member listing AFTER the `: <Sig>`
                // annotation): skip `: <Sig>` / `<: <Sig>` pairs so the body
                // tokens decide the shape.
                let mut i = name_idx + 1;
                // ROOT prints of bodiless-by-construction modules come FIRST,
                // before the seal-skip loop would eat their `: Sig` opener:
                //
                // - `Module <path> : Sig <members> End := <target>` — a module
                //   minted by a functor APPLICATION (`Module PositiveMap.ME :
                //   Sig ... End := (OrderedType.KeyOrderedType PositiveMap.E)`,
                //   verified live) or reached by ALIAS (`Module NBinary : Sig
                //   ... End := N`). `Print Module` has no syntactic Struct body
                //   to show, so it prints the RESOLVED signature — but the
                //   members are real, fully-qualified-queryable global kernel
                //   constants (`Check ...ME.eqk` answers). Open an ENUMERATING
                //   region and flag the listing `root_instantiated` so every
                //   member is marked `speculative` (dumped VALUE-BEARING with
                //   the fail-closed `Speculative` marker: a functor/alias-
                //   generated value the Clean kernel may not reduce through
                //   becomes a clean type-only axiom on rejection, not the masked
                //   taint the bare-value-bearing enumeration hit). Without this
                //   prong the header sentence would bail at `: Sig` after
                //   queuing a bogus `<path>.<path>` submodule, dropping the
                //   first member (`ME.eqk`) and never recursing into the nested
                //   modules (`ME.MO` and its ~60-member tower). This is a STRICT
                //   SUPERSET of main's enumeration: later member sentences
                //   enumerate at the same prefix (the module path), so no
                //   previously-dumped name is lost.
                //
                // - `Module <path> : Funsig (X:SIG) ... Sig <spec> End` — a
                //   functor reached by ALIAS: members are functor-scoped
                //   (`MPbound`). Mirror the `:= Functor` arm — record +
                //   suppress. Without this, the unopened region would leak
                //   every spec member as a bogus root candidate.
                // (Stack is empty here, so the region prefix is the module's
                // own full logical path — root prints show only the LAST path
                // segment in the header.)
                if stack.is_empty() && toks.get(i) == Some(&":") {
                    // GUARD: a genuine instantiated sig opens directly onto its
                    // members (`: Sig Module …` / `: Sig Definition …` / `: Sig
                    // End`), never onto a `:=` — so a sealed struct whose
                    // signature happened to be named `Sig` (`Module X : Sig :=
                    // Struct …`) can never misfire the enumerating region and
                    // drop X's real struct members.
                    if toks.get(i + 1) == Some(&"Sig") && toks.get(i + 2) != Some(&":=") && !is_type
                    {
                        listing.root_instantiated = true;
                        stack.push((module.to_string(), false));
                        toks = &toks[i + 2..];
                        continue;
                    }
                    if toks.get(i + 1) == Some(&"Funsig") {
                        listing.functors.push(module.to_string());
                        stack.push((module.to_string(), true));
                        let mut j = i + 1;
                        while toks.get(j).is_some_and(|t| *t != "Struct" && *t != "Sig") {
                            j += 1;
                        }
                        if toks.get(j).is_none() {
                            return;
                        }
                        toks = &toks[j + 1..];
                        continue;
                    }
                }
                while matches!(toks.get(i), Some(&":") | Some(&"<:")) {
                    i += 2;
                }
                // Prefix for an inline-expanded body. Outermost region:
                // `Print Module M` prints `Module <last segment> ...`; the
                // prefix is the full logical path.
                let prefix = match stack.last() {
                    None => module.to_string(),
                    Some((parent, _)) => format!("{parent}.{name}"),
                };
                // Only the tokens immediately after the name/ascription decide
                // the shape (`:= Struct`/`:= Sig`/`:= Functor`/`:= Alias`/
                // bodyless); scanning farther would misfire on a later
                // module's `Struct`.
                if toks.get(i) == Some(&":=")
                    && matches!(toks.get(i + 1), Some(&"Struct") | Some(&"Sig"))
                {
                    // Inline-expanded body: open a Struct/Sig region.
                    let is_sig = is_type || toks[i + 1] == "Sig" || in_sig(stack);
                    stack.push((prefix, is_sig));
                    toks = &toks[i + 2..];
                } else if toks.get(i) == Some(&":=") && toks.get(i + 1) == Some(&"Functor") {
                    // Functor (verified live on Coq.Structures.OrderedTypeEx.
                    // PairOrderedType: `Module PairOrderedType := Functor
                    // (O1:OrderedType.OrderedType) ... Struct ... End`):
                    // members are functor-scoped, not global kernel constants.
                    // Record the functor and open a SUPPRESSING (sig-like)
                    // region so its members are neither emitted nor queued;
                    // the region's single `End` keeps the stack balanced.
                    if !in_sig(stack) {
                        listing.functors.push(prefix.clone());
                    }
                    stack.push((prefix, true));
                    // Skip the functor binder tokens up to the body opener.
                    // When the opener is beyond this sentence the remaining
                    // tokens are binders; later sentences' body tokens are
                    // scanned normally under the suppressing region.
                    let mut j = i + 1;
                    while toks.get(j).is_some_and(|t| *t != "Struct" && *t != "Sig") {
                        j += 1;
                    }
                    if toks.get(j).is_none() {
                        return;
                    }
                    toks = &toks[j + 1..];
                } else if toks.get(i) == Some(&":=") {
                    // `Module N := Other.Path` alias: skip the target token.
                    toks = &toks[i + 2..];
                } else {
                    // Bodyless nested module line (`Print Module` does not
                    // expand nested modules): queue for a recursive print.
                    if !is_type && !in_sig(stack) && !name.is_empty() {
                        listing
                            .submodules
                            .push(format!("{}.{name}", current_prefix(stack, module)));
                    }
                    toks = &toks[name_idx + 1..];
                }
            }
            _ if CONSTANT_KEYWORDS.contains(&kw) || INDUCTIVE_KEYWORDS.contains(&kw) => {
                let Some(raw_name) = toks.get(1) else {
                    return;
                };
                // Universe-polymorphic declarations print a `@{u ...}` universe
                // annotation right after the name (`Class Equivalence@{u u0}
                // ...`). It contains a space, so whitespace tokenization glues a
                // truncated `@{u` onto the name token (leaving the rest as stray
                // tokens). Strip from `@{` so the candidate is the bare
                // identifier the `Definition`/`TypeOf`/`MInd` queries expect —
                // otherwise every universe-polymorphic Record/Class is looked up
                // under a bogus name and skipped as `no-definition-no-typeof`.
                let raw_name = raw_name.split("@{").next().unwrap_or(raw_name);
                let name = raw_name.trim_end_matches([':', ',', '(', '{']);
                // Inside a Module Type / Sig specification: advance without
                // emitting (so a trailing `End` in the same sentence is seen).
                if !in_sig(stack) && !name.is_empty() {
                    listing.candidates.push(Candidate {
                        qualified: format!("{}.{name}", current_prefix(stack, module)),
                        keyword: kw.to_string(),
                        // An instantiated-module (functor-application) member:
                        // fresh global constant, dumped value-bearing with the
                        // fail-closed `Speculative` marker.
                        speculative: listing.root_instantiated,
                    });
                }
                toks = &toks[2..];
            }
            // Anything else (a type after `<keyword> <name> :`, notation
            // text, ...) ends the scan of this sentence.
            _ => return,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(l: &Listing) -> Vec<&str> {
        l.candidates.iter().map(|c| c.qualified.as_str()).collect()
    }

    fn speculative_names(l: &Listing) -> Vec<&str> {
        l.candidates
            .iter()
            .filter(|c| c.speculative)
            .map(|c| c.qualified.as_str())
            .collect()
    }

    #[test]
    fn test_parse_module_listing_functor_application_root_enumerates_speculative() {
        // Real `Print Module Coq.FSets.FMapPositive.PositiveMap.ME` shape
        // (verified live 2026-07-14): a functor-APPLICATION module has no
        // syntactic body, so the root print shows the resolved signature
        // `: Sig ... End := (F X)` — parenthesized target, so NOT an alias.
        // Its members are real global kernel constants (`Check ...ME.eqk`
        // answers) but functor-generated: every one must enumerate as a
        // `speculative` candidate (dumped VALUE-BEARING with the fail-closed
        // `Speculative` marker). Without this prong the header sentence bails
        // at `: Sig` and drops the first member (`eqk`) plus the nested `MO`.
        let text = "Module PositiveMap.ME : Sig Module MO \
             Definition eqk : forall elt : Type, positive * elt -> Prop. \
             Parameter eqke_eqk : forall elt : Type, eqke x x' -> eqk x x'. \
             End := (OrderedType.KeyOrderedType PositiveMap.E)";
        let l = parse_module_listing(text, "Coq.FSets.FMapPositive.PositiveMap.ME");
        assert_eq!(
            names(&l),
            vec![
                "Coq.FSets.FMapPositive.PositiveMap.ME.eqk",
                "Coq.FSets.FMapPositive.PositiveMap.ME.eqke_eqk",
            ],
            "functor-application members must enumerate (incl. the header-sentence eqk)"
        );
        assert_eq!(
            speculative_names(&l),
            names(&l),
            "every functor-application member is dumped Speculative"
        );
        assert!(l.root_instantiated);
        assert_eq!(
            l.submodules,
            vec!["Coq.FSets.FMapPositive.PositiveMap.ME.MO".to_string()],
            "nested instantiated modules must queue for recursion"
        );
        assert!(l.functors.is_empty());
    }

    #[test]
    fn test_parse_module_listing_natsort_application_enumerates_speculative() {
        // Real `Print Module Coq.Sorting.Mergesort.NatSort` tail (verified
        // live 2026-07-14): `End := (Sort NatOrder)` — parenthesized, so it
        // mints fresh constants and must ENUMERATE speculative.
        let text = "Module NatSort : Sig \
             Definition merge : list nat -> list nat -> list nat. \
             Definition sort : list nat -> list nat. \
             End := (Sort NatOrder)";
        let l = parse_module_listing(text, "Coq.Sorting.Mergesort.NatSort");
        assert_eq!(
            names(&l),
            vec![
                "Coq.Sorting.Mergesort.NatSort.merge",
                "Coq.Sorting.Mergesort.NatSort.sort",
            ]
        );
        assert_eq!(speculative_names(&l), names(&l));
    }

    #[test]
    fn test_parse_module_listing_alias_root_enumerated_speculative_not_emptied() {
        // Real `Print Module Coq.PArith.POrderedType.Positive_as_OT` shape
        // (verified live 2026-07-14): a pure module alias prints the resolved
        // signature then `End := BinPos.Pos` (a BARE-PATH target). Unlike a
        // functor application it mints no fresh values of its own, but its
        // members ARE fully-qualified-queryable global constants that main's
        // stack-empty fallback already enumerates (e.g. NBinary's 1327
        // `NBinary.N.*`). The prong must ENUMERATE them (marked speculative) —
        // NOT empty the listing: emptying would drop every baseline-KV member
        // of the alias (measured NBinary 1327 → 0, a regression). The alias
        // shape is handled identically to the application shape.
        let text = "Module Positive_as_OT : Sig \
             Definition t : Set. \
             Definition succ : positive -> positive. \
             End := BinPos.Pos";
        let l = parse_module_listing(text, "Coq.PArith.POrderedType.Positive_as_OT");
        assert_eq!(
            names(&l),
            vec![
                "Coq.PArith.POrderedType.Positive_as_OT.t",
                "Coq.PArith.POrderedType.Positive_as_OT.succ",
            ],
            "alias members must still enumerate (never emptied)"
        );
        assert_eq!(speculative_names(&l), names(&l));
        assert!(l.root_instantiated);
    }

    #[test]
    fn test_parse_module_listing_funsig_root_suppressed_as_functor() {
        // A functor reached by alias prints `: Funsig (M:WS) Sig <spec> End`.
        // Members are functor-scoped (`MPbound`) — they must NOT leak as root
        // candidates (the unopened region would produce bogus skips).
        let text = "Module Properties : Funsig (M:WS) Sig Module Dec Module FM \
             Parameter In_dec : forall (x : M.elt) (s : M.t), {M.In x s}. \
             Definition Add : M.E.t -> M.t -> M.t -> Prop. \
             End";
        let l = parse_module_listing(text, "Coq.FSets.FSetProperties.Properties");
        assert!(names(&l).is_empty(), "functor members are not global");
        assert!(l.submodules.is_empty(), "functor-spec modules not queued");
        assert_eq!(
            l.functors,
            vec!["Coq.FSets.FSetProperties.Properties".to_string()]
        );
    }

    #[test]
    fn test_parse_module_listing_struct_members_are_not_speculative() {
        // A NORMAL `:= Struct` module's members keep `speculative = false`
        // (dumped value-bearing WITHOUT the marker): the instantiated-root flag
        // must never leak onto ordinary struct listings.
        let text = "Module PositiveSet := Struct Module E \
             Definition mem : elt -> t -> bool. \
             Definition add : elt -> t -> t. End";
        let l = parse_module_listing(text, "Coq.MSets.MSetPositive.PositiveSet");
        assert_eq!(
            names(&l),
            vec![
                "Coq.MSets.MSetPositive.PositiveSet.mem",
                "Coq.MSets.MSetPositive.PositiveSet.add",
            ]
        );
        assert!(
            speculative_names(&l).is_empty(),
            "struct members are value-bearing, never speculative"
        );
        assert!(!l.root_instantiated);
        assert_eq!(
            l.submodules,
            vec!["Coq.MSets.MSetPositive.PositiveSet.E".to_string()]
        );
    }

    #[test]
    fn test_parse_module_listing_sealed_struct_named_sig_not_misfired() {
        // A sealed struct whose signature is literally named `Sig`
        // (`Module X : Sig := Struct …`) must NOT open the enumerating region:
        // the `toks[i+2] != ":="` guard excludes it, so its real struct members
        // enumerate normally and non-speculative.
        let text = "Module X : Sig := Struct \
             Definition a : nat. Definition b : nat. End";
        let l = parse_module_listing(text, "Coq.Test.X");
        assert!(
            !l.root_instantiated,
            "a sealed :=Struct is not instantiated"
        );
        assert_eq!(names(&l), vec!["Coq.Test.X.a", "Coq.Test.X.b"]);
        assert!(speculative_names(&l).is_empty());
    }

    #[test]
    fn test_parse_module_listing_logic_like_extracts_names() {
        let text = "Module Logic := Struct Inductive True : Prop :=   I : True. \
             Definition True_rect : forall P : Type, P -> True -> P. \
             Inductive False : Prop :=   . \
             Definition not : Prop -> Prop. \
             Parameter proj1 : forall A B : Prop, A /\\ B -> A. \
             Parameter f_pred : forall x y : nat, x = y -> Nat.pred x = Nat.pred y. \
             End";
        let l = parse_module_listing(text, "Coq.Init.Logic");
        assert_eq!(
            names(&l),
            vec![
                "Coq.Init.Logic.True",
                "Coq.Init.Logic.True_rect",
                "Coq.Init.Logic.False",
                "Coq.Init.Logic.not",
                "Coq.Init.Logic.proj1",
                "Coq.Init.Logic.f_pred",
            ]
        );
        assert_eq!(l.candidates[0].keyword, "Inductive");
        assert!(l.submodules.is_empty());
    }

    #[test]
    fn test_parse_module_listing_strips_universe_annotation_from_name() {
        // Universe-polymorphic declarations print a `@{u ...}` annotation glued
        // to the name; the space inside it means whitespace tokenization yields
        // a truncated `Equivalence@{u` name token (with stray `u0}` after). The
        // candidate must be the bare identifier, else the SerAPI lookups miss
        // and the whole Record/Class/Inductive is dropped (the bug fixed at the
        // `split("@{")` in process_statement). Covers a multi-token annotation.
        let text = "Module CRelationClasses := Struct \
             Class Equivalence@{u u0} (A : Type@{u}) (R : crelation A) : Prop. \
             Inductive Im@{u u0 u1} (U : Type) : Ensemble. \
             Definition plain : nat. End";
        let l = parse_module_listing(text, "Coq.Classes.CRelationClasses");
        assert_eq!(
            names(&l),
            vec![
                "Coq.Classes.CRelationClasses.Equivalence",
                "Coq.Classes.CRelationClasses.Im",
                "Coq.Classes.CRelationClasses.plain",
            ],
            "universe annotations must be stripped from candidate names"
        );
    }

    #[test]
    fn test_parse_module_listing_inline_nested_module_prefixes() {
        let text = "Module PeanoNat := Struct Module Nat := Struct \
             Definition add : nat -> nat -> nat. End \
             Definition outer : nat. End";
        let l = parse_module_listing(text, "Coq.Arith.PeanoNat");
        assert_eq!(
            names(&l),
            vec!["Coq.Arith.PeanoNat.Nat.add", "Coq.Arith.PeanoNat.outer"]
        );
    }

    #[test]
    fn test_parse_module_listing_bodyless_submodule_queued() {
        // Real `Print Module Coq.Arith.PeanoNat` shape: nested modules print
        // as a bodyless `Module Nat` line inside the same sentence as the
        // next declaration.
        let text = "Module PeanoNat := Struct Module Nat \
             Definition lt_n : forall n m : nat, n < S m -> n <= m. \
             Definition pred_of : forall n : nat, Nat.pred n = n - 1. End";
        let l = parse_module_listing(text, "Coq.Arith.PeanoNat");
        assert_eq!(
            names(&l),
            vec!["Coq.Arith.PeanoNat.lt_n", "Coq.Arith.PeanoNat.pred_of"]
        );
        assert_eq!(l.submodules, vec!["Coq.Arith.PeanoNat.Nat".to_string()]);
    }

    #[test]
    fn test_parse_module_listing_module_type_body_skipped() {
        let text = "Module M := Struct Module Type T := Sig Parameter ghost : nat. End \
             Definition real : nat. End";
        let l = parse_module_listing(text, "Coq.X.M");
        assert_eq!(names(&l), vec!["Coq.X.M.real"]);
        assert!(l.submodules.is_empty());
    }

    #[test]
    fn test_parse_module_listing_end_then_decl_same_sentence() {
        let text = "Module M := Struct Module N := Struct Definition inner : nat. \
             End Definition after : nat. End";
        let l = parse_module_listing(text, "Coq.X.M");
        assert_eq!(names(&l), vec!["Coq.X.M.N.inner", "Coq.X.M.after"]);
    }

    #[test]
    fn test_parse_module_listing_compact_inner_module_chains() {
        // Real `Print Module Coq.Arith.PeanoNat.Nat` shape: inner modules
        // print a compact name-only listing with NO sentence dots.
        let text = "Module Nat := Struct Definition t Definition zero Definition add \
             Module Private_OrderTac Parameter le_trans Inductive parity End";
        let l = parse_module_listing(text, "Coq.Arith.PeanoNat.Nat");
        assert_eq!(
            names(&l),
            vec![
                "Coq.Arith.PeanoNat.Nat.t",
                "Coq.Arith.PeanoNat.Nat.zero",
                "Coq.Arith.PeanoNat.Nat.add",
                "Coq.Arith.PeanoNat.Nat.le_trans",
                "Coq.Arith.PeanoNat.Nat.parity",
            ]
        );
        assert_eq!(
            l.submodules,
            vec!["Coq.Arith.PeanoNat.Nat.Private_OrderTac".to_string()]
        );
    }

    #[test]
    fn test_parse_module_listing_sealed_signature_members_enumerated() {
        // Real `Print Module Coq.Reals.Rdefinitions.RbaseSymbolsImpl` shape
        // (verified live): a sealed module prints `: <Sig>` between the name
        // and `:= Struct`, and its full member listing follows.
        let text = "Module RbaseSymbolsImpl : RbaseSymbolsSig := Struct \
             Definition R : Set. \
             Definition Rplus : R -> R -> R. \
             End";
        let l = parse_module_listing(text, "Coq.Reals.Rdefinitions.RbaseSymbolsImpl");
        assert_eq!(
            names(&l),
            vec![
                "Coq.Reals.Rdefinitions.RbaseSymbolsImpl.R",
                "Coq.Reals.Rdefinitions.RbaseSymbolsImpl.Rplus",
            ]
        );
        assert!(l.submodules.is_empty(), "sealed header must not self-queue");
        assert!(l.functors.is_empty());
    }

    #[test]
    fn test_parse_module_listing_functor_suppressed_and_recorded() {
        // Real `Print Module Coq.Structures.OrderedTypeEx.PairOrderedType`
        // shape (verified live): functor binders precede the Struct body;
        // members are functor-scoped and must not become candidates.
        let text = "Module PairOrderedType := Functor (O1:OrderedType.OrderedType) \
             Functor (O2:OrderedType.OrderedType) Struct Module MO1 Module MO2 \
             Definition t : Type. \
             Parameter eq_refl : forall x : t, eq x x. \
             End";
        let l = parse_module_listing(text, "Coq.Structures.OrderedTypeEx.PairOrderedType");
        assert!(names(&l).is_empty(), "functor members are not global");
        assert!(l.submodules.is_empty(), "functor-body modules not queued");
        assert_eq!(
            l.functors,
            vec!["Coq.Structures.OrderedTypeEx.PairOrderedType".to_string()]
        );
    }

    #[test]
    fn test_parse_module_listing_functor_then_sibling_decl() {
        // The functor region's End must pop its frame so a sibling
        // declaration after it lands at the outer prefix.
        let text = "Module M := Struct Module F := Functor (X:SIG) Struct \
             Definition inner : nat. End Definition after : nat. End";
        let l = parse_module_listing(text, "Coq.X.M");
        assert_eq!(names(&l), vec!["Coq.X.M.after"]);
        assert_eq!(l.functors, vec!["Coq.X.M.F".to_string()]);
    }

    #[test]
    fn test_split_sentences_keeps_qualified_dots() {
        let s = split_sentences("Parameter p : Nat.pred x = y. End");
        assert_eq!(s, vec!["Parameter p : Nat.pred x = y", " End"]);
    }

    #[test]
    fn test_extract_message_str_reads_str_field() {
        let line = r#"(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Notice)(loc())(pp(Pp_string x))(str"Module X := Struct End")))))"#;
        let text = extract_message_str(&[line.to_string()]).expect("should find str field");
        assert_eq!(text, "Module X := Struct End");
    }

    /// Warning/Info messages emitted while a query runs are diagnostics, not
    /// payload, and must NOT be concatenated into the extracted text. The
    /// measured regression: `Print Module mathcomp.algebra.rat` (with the
    /// module's notations Imported) emits a `notation-overridden` Warning
    /// whose tail token `[notation-overridden,parsing,default]` glued onto
    /// the same dot-less sentence as `Module rat := Struct Record rat ...`,
    /// so the unknown token aborted the sentence and the `rat` inductive was
    /// silently dropped from enumeration (no skip entry).
    #[test]
    fn test_extract_message_str_ignores_warning_and_info_levels() {
        let warning = r#"(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Warning)(loc())(pp(Pp_string x))(str"Notation \"[ rat _ // _ ]\" was already used in scope ring_scope.\n[notation-overridden,parsing,default]")))))"#;
        let info = r#"(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Info)(loc())(pp(Pp_string x))(str"[Loading ML file ring_plugin.cmxs ... done]")))))"#;
        let notice = r#"(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Notice)(loc())(pp(Pp_string x))(str"Module rat := Struct Record rat : Set := Rat { valq : T } End")))))"#;
        let text =
            extract_message_str(&[warning.to_string(), info.to_string(), notice.to_string()])
                .expect("notice text should extract");
        assert_eq!(
            text, "Module rat := Struct Record rat : Set := Rat { valq : T } End",
            "warning/info diagnostics must not pollute the listing"
        );
        let l = parse_module_listing(&text, "mathcomp.algebra.rat");
        assert_eq!(
            names(&l),
            vec!["mathcomp.algebra.rat.rat"],
            "the rat record must enumerate once diagnostics are filtered"
        );
        // Warning-only feedback extracts nothing (never a bogus listing).
        assert_eq!(extract_message_str(&[warning.to_string()]), None);
    }
}
