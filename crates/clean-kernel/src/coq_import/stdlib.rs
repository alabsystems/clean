// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Coq stdlib alias tables used by the import scaffold.

/// Mapping from one or more Coq stdlib type aliases onto a Lean core name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CoqStdlibTypeMapping {
    pub coq_aliases: &'static [&'static str],
    pub lean_name: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct CoqStdlibGlobalMapping {
    pub coq_aliases: &'static [&'static str],
    pub lean_name: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct CoqStdlibInductiveMapping {
    pub coq_aliases: &'static [&'static str],
    pub lean_name: &'static str,
    pub constructors: &'static [&'static str],
    pub projections: &'static [&'static str],
}

/// Coq stdlib type-like aliases recognized by the import scaffold.
pub const COQ_STDLIB_TYPE_MAPPINGS: &[CoqStdlibTypeMapping] = &[
    CoqStdlibTypeMapping {
        coq_aliases: &[
            "nat",
            "Datatypes.nat",
            "Coq.Init.Datatypes.nat",
            "Coq.Arith.PeanoNat.Nat",
        ],
        lean_name: "Nat",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["bool", "Datatypes.bool", "Coq.Init.Datatypes.bool"],
        lean_name: "Bool",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &[
            "list",
            "Datatypes.list",
            "Coq.Init.Datatypes.list",
            "Coq.Lists.List.list",
        ],
        lean_name: "List",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["option", "Datatypes.option", "Coq.Init.Datatypes.option"],
        lean_name: "Option",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["prod", "Datatypes.prod", "Coq.Init.Datatypes.prod"],
        lean_name: "Prod",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["sum", "Datatypes.sum", "Coq.Init.Datatypes.sum"],
        lean_name: "Sum",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["unit", "Datatypes.unit", "Coq.Init.Datatypes.unit"],
        lean_name: "Unit",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &[
            "Z",
            "BinNums.Z",
            "Coq.Numbers.BinNums.Z",
            "Coq.ZArith.BinInt.Z",
        ],
        lean_name: "Int",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &[
            "positive",
            "BinNums.positive",
            "Coq.Numbers.BinNums.positive",
        ],
        lean_name: "Nat",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["sig", "Specif.sig", "Coq.Init.Specif.sig"],
        lean_name: "Subtype",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["sigT", "Specif.sigT", "Coq.Init.Specif.sigT"],
        lean_name: "Sigma",
    },
    CoqStdlibTypeMapping {
        coq_aliases: &["eq", "Logic.eq", "Coq.Init.Logic.eq"],
        lean_name: "Eq",
    },
];

pub(crate) const COQ_STDLIB_TERM_MAPPINGS: &[CoqStdlibGlobalMapping] = &[
    CoqStdlibGlobalMapping {
        coq_aliases: &["O", "Datatypes.O", "Coq.Init.Datatypes.O"],
        lean_name: "Nat.zero",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["S", "Datatypes.S", "Coq.Init.Datatypes.S"],
        lean_name: "Nat.succ",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["true", "Datatypes.true", "Coq.Init.Datatypes.true"],
        lean_name: "Bool.true",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["false", "Datatypes.false", "Coq.Init.Datatypes.false"],
        lean_name: "Bool.false",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["nil", "Datatypes.nil", "Coq.Init.Datatypes.nil"],
        lean_name: "List.nil",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["cons", "Datatypes.cons", "Coq.Init.Datatypes.cons"],
        lean_name: "List.cons",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["None", "Datatypes.None", "Coq.Init.Datatypes.None"],
        lean_name: "Option.none",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["Some", "Datatypes.Some", "Coq.Init.Datatypes.Some"],
        lean_name: "Option.some",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["pair", "Datatypes.pair", "Coq.Init.Datatypes.pair"],
        lean_name: "Prod.mk",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["inl", "Datatypes.inl", "Coq.Init.Datatypes.inl"],
        lean_name: "Sum.inl",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["inr", "Datatypes.inr", "Coq.Init.Datatypes.inr"],
        lean_name: "Sum.inr",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["tt", "Datatypes.tt", "Coq.Init.Datatypes.tt"],
        lean_name: "Unit.unit",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["exist", "Specif.exist", "Coq.Init.Specif.exist"],
        lean_name: "Subtype.mk",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["existT", "Specif.existT", "Coq.Init.Specif.existT"],
        lean_name: "Sigma.mk",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["eq_refl", "Logic.eq_refl", "Coq.Init.Logic.eq_refl"],
        lean_name: "Eq.refl",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &[
            "le",
            "Peano.le",
            "Coq.Init.Peano.le",
            "Nat.le",
            "Coq.Arith.PeanoNat.Nat.le",
        ],
        lean_name: "Nat.le",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &[
            "lt",
            "Peano.lt",
            "Coq.Init.Peano.lt",
            "Nat.lt",
            "Coq.Arith.PeanoNat.Nat.lt",
        ],
        lean_name: "Nat.lt",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &[
            "plus",
            "Peano.plus",
            "Coq.Init.Peano.plus",
            "Nat.add",
            "Coq.Arith.PeanoNat.Nat.add",
        ],
        lean_name: "Nat.add",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &[
            "mult",
            "Peano.mult",
            "Coq.Init.Peano.mult",
            "Nat.mul",
            "Coq.Arith.PeanoNat.Nat.mul",
        ],
        lean_name: "Nat.mul",
    },
];

pub(crate) const COQ_STDLIB_INDUCTIVE_MAPPINGS: &[CoqStdlibInductiveMapping] = &[
    CoqStdlibInductiveMapping {
        coq_aliases: &[
            "nat",
            "Datatypes.nat",
            "Coq.Init.Datatypes.nat",
            "Coq.Arith.PeanoNat.Nat",
        ],
        lean_name: "Nat",
        constructors: &["Nat.zero", "Nat.succ"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["bool", "Datatypes.bool", "Coq.Init.Datatypes.bool"],
        lean_name: "Bool",
        constructors: &["Bool.false", "Bool.true"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &[
            "list",
            "Datatypes.list",
            "Coq.Init.Datatypes.list",
            "Coq.Lists.List.list",
        ],
        lean_name: "List",
        constructors: &["List.nil", "List.cons"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["option", "Datatypes.option", "Coq.Init.Datatypes.option"],
        lean_name: "Option",
        constructors: &["Option.none", "Option.some"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["prod", "Datatypes.prod", "Coq.Init.Datatypes.prod"],
        lean_name: "Prod",
        constructors: &["Prod.mk"],
        projections: &["Prod.fst", "Prod.snd"],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["sum", "Datatypes.sum", "Coq.Init.Datatypes.sum"],
        lean_name: "Sum",
        constructors: &["Sum.inl", "Sum.inr"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["unit", "Datatypes.unit", "Coq.Init.Datatypes.unit"],
        lean_name: "Unit",
        constructors: &["Unit.unit"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &[
            "Z",
            "BinNums.Z",
            "Coq.Numbers.BinNums.Z",
            "Coq.ZArith.BinInt.Z",
        ],
        lean_name: "Int",
        constructors: &[],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &[
            "positive",
            "BinNums.positive",
            "Coq.Numbers.BinNums.positive",
        ],
        lean_name: "Nat",
        constructors: &[],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["sig", "Specif.sig", "Coq.Init.Specif.sig"],
        lean_name: "Subtype",
        constructors: &["Subtype.mk"],
        projections: &["Subtype.val", "Subtype.property"],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["sigT", "Specif.sigT", "Coq.Init.Specif.sigT"],
        lean_name: "Sigma",
        constructors: &["Sigma.mk"],
        projections: &["Sigma.fst", "Sigma.snd"],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["eq", "Logic.eq", "Coq.Init.Logic.eq"],
        lean_name: "Eq",
        constructors: &["Eq.refl"],
        projections: &[],
    },
];

pub(crate) const COQ_STDLIB_PROPOSITION_MAPPINGS: &[CoqStdlibGlobalMapping] = &[
    CoqStdlibGlobalMapping {
        coq_aliases: &["True", "Logic.True", "Coq.Init.Logic.True"],
        lean_name: "True",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["False", "Logic.False", "Coq.Init.Logic.False"],
        lean_name: "False",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["and", "Logic.and", "Coq.Init.Logic.and"],
        lean_name: "And",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["or", "Logic.or", "Coq.Init.Logic.or"],
        lean_name: "Or",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["not", "Logic.not", "Coq.Init.Logic.not"],
        lean_name: "Not",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["iff", "Logic.iff", "Coq.Init.Logic.iff"],
        lean_name: "Iff",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["ex", "Logic.ex", "Coq.Init.Logic.ex"],
        lean_name: "Exists",
    },
];

pub(crate) const COQ_STDLIB_PROPOSITION_TERM_MAPPINGS: &[CoqStdlibGlobalMapping] = &[
    CoqStdlibGlobalMapping {
        coq_aliases: &["I", "Logic.I", "Coq.Init.Logic.I"],
        lean_name: "True.intro",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &[
            "False_rect",
            "Logic.False_rect",
            "Coq.Init.Logic.False_rect",
        ],
        lean_name: "False.elim",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["conj", "Logic.conj", "Coq.Init.Logic.conj"],
        lean_name: "And.intro",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["or_introl", "Logic.or_introl", "Coq.Init.Logic.or_introl"],
        lean_name: "Or.inl",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["or_intror", "Logic.or_intror", "Coq.Init.Logic.or_intror"],
        lean_name: "Or.inr",
    },
    CoqStdlibGlobalMapping {
        coq_aliases: &["ex_intro", "Logic.ex_intro", "Coq.Init.Logic.ex_intro"],
        lean_name: "Exists.intro",
    },
];

pub(crate) const COQ_STDLIB_PROPOSITION_INDUCTIVE_MAPPINGS: &[CoqStdlibInductiveMapping] = &[
    CoqStdlibInductiveMapping {
        coq_aliases: &["True", "Logic.True", "Coq.Init.Logic.True"],
        lean_name: "True",
        constructors: &["True.intro"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["False", "Logic.False", "Coq.Init.Logic.False"],
        lean_name: "False",
        constructors: &[],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["and", "Logic.and", "Coq.Init.Logic.and"],
        lean_name: "And",
        constructors: &["And.intro"],
        projections: &["And.left", "And.right"],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["or", "Logic.or", "Coq.Init.Logic.or"],
        lean_name: "Or",
        constructors: &["Or.inl", "Or.inr"],
        projections: &[],
    },
    CoqStdlibInductiveMapping {
        coq_aliases: &["ex", "Logic.ex", "Coq.Init.Logic.ex"],
        lean_name: "Exists",
        constructors: &["Exists.intro"],
        projections: &[],
    },
];
