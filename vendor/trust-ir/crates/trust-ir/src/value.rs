// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

macro_rules! typed_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        pub struct $name(pub u32);

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }

        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl $name {
            pub const fn new(index: u32) -> Self {
                Self(index)
            }

            pub const fn index(self) -> u32 {
                self.0
            }

            pub const fn as_usize(self) -> usize {
                self.0 as usize
            }
        }
    };
}

typed_id!(
    /// SSA value reference. Index into a function's value table.
    ValueId
);

typed_id!(
    /// Basic block reference. Index into a function's block list.
    BlockId
);

typed_id!(
    /// Function reference. Index into a module's function list.
    FuncId
);

typed_id!(
    /// Struct definition reference. Index into a module's struct table.
    StructId
);

typed_id!(
    /// Type reference. Index into a module's type table.
    TyId
);

typed_id!(
    /// Function type reference. Index into a module's func type table.
    FuncTyId
);

typed_id!(
    /// Enum definition reference. Index into a module's enum table.
    EnumId
);

typed_id!(
    /// Global definition reference. Index into a module's `globals` table.
    ///
    /// Materialized as an SSA pointer by `Inst::GlobalAddr`. A frontend lowers
    /// `&STATIC`, a `&str` literal's backing data, and a trait-object vtable
    /// reference to a `GlobalAddr` of the corresponding `GlobalId`; `trust-cg`
    /// emits a relocation to the data/rodata symbol named by that global.
    GlobalId
);

typed_id!(
    /// Proof annotation reference. Index into a module's proof table.
    ProofId
);

typed_id!(
    /// Custom proof tag for extensible proof annotations.
    ProofTag
);

typed_id!(
    /// Binding frame reference.
    ///
    /// Identifies a binding frame — a typed record of SSA slots used to
    /// lower quantifier bodies (`\E i \in S : P(i)`, `\A i \in S : P(i)`).
    /// Each `Inst::OpenFrame` declares a fresh `BindingFrameId` that is
    /// unique within the enclosing function.
    ///
    /// Binding frames are SSA values (not memory) so backends can lower
    /// them to either stack allocations (CPU) or per-lane register banks
    /// (GPU). See `designs/2026-04-18-ty-supremacy-trust-ir-scope.md` §R4.
    BindingFrameId
);

typed_id!(
    /// Record definition reference. Index into a module's record table.
    ///
    /// Records (ty-style) differ from structs: they have named fields but no
    /// fixed layout, no offset/size/align metadata, and equality is by
    /// field-set rather than memory layout. Frontends that need C-style layout
    /// should use `StructId` instead.
    RecordId
);

typed_id!(
    /// Refinement predicate reference. Index into a module's `predicates`
    /// table (see [`crate::pred::Pred`]).
    ///
    /// **Content-interned.** Unlike `StructId`/`EnumId`/`RecordId`, whose
    /// definitions carry a name and therefore a producer-chosen identity, a
    /// `PredId` is a pure function of the predicate's CONTENT: two predicates
    /// with the same meaning are the same id no matter which proof, pass or
    /// frontend minted them. That is not a convenience — it is the structural
    /// fix for the join-drop miscompile class, where two carriers over an
    /// identical universe failed to merge at a control-flow join because they
    /// had been cited by different proofs, the shape was dropped, and the
    /// value silently reverted to the raw encoding convention. Mint one with
    /// [`crate::Module::intern_pred`]; the validator rejects a `predicates`
    /// table containing duplicate content.
    PredId
);

typed_id!(
    /// Universe reference. Index into a module's `universes` table (see
    /// [`crate::pred::Universe`]).
    ///
    /// Content-interned for exactly the reason [`PredId`] is: a universe's
    /// identity is its extension and nothing else. Mint one with
    /// [`crate::Module::intern_universe`].
    UnivId
);

typed_id!(
    /// Closure type reference. Index into a module's closure type table.
    ///
    /// A closure is a first-class function value bundled with a captured
    /// environment (see `ClosureTy` in `ty`). Bare function-pointer types
    /// (no captures) use `FuncTyId` directly.
    ClosureTyId
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceSpan {
    pub file: u32,
    pub line: u32,
    pub col: u32,
}

/// One entry in a function's LEXICAL SCOPE TREE (v33).
///
/// A scope is the debug-info notion, not the SSA one: it records where in the
/// SOURCE a name became visible, so a debugger stopped at an instruction can be
/// told which bindings are in scope there. SSA values are function-unique and
/// scope-free; this table sits beside them as claim-style metadata and carries
/// no operational semantics.
///
/// INVARIANTS (checked by the consumer, which fails closed rather than trusting
/// them — a producer bug must not become a debugger lie):
/// * index `0` is the OUTERMOST scope and is the only one with `parent: None`;
/// * every other entry has `parent: Some(p)` with `p <` its own index.
///
/// The `p < index` rule makes the table topologically ordered by construction,
/// so acyclicity is a range check rather than a traversal — and a consumer can
/// build its own tree in one forward pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScopeData {
    /// Enclosing scope index, or `None` for the outermost scope.
    pub parent: Option<u32>,
    /// Where the scope OPENS. `None` when the producer had no usable location.
    pub span: Option<SourceSpan>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_id_construction_and_index() {
        let v = ValueId::new(42);
        assert_eq!(v.index(), 42);
        assert_eq!(v.as_usize(), 42);
        assert_eq!(v.0, 42);
    }

    #[test]
    fn block_id_construction_and_index() {
        let b = BlockId::new(7);
        assert_eq!(b.index(), 7);
        assert_eq!(b.as_usize(), 7);
    }

    #[test]
    fn func_id_construction_and_index() {
        let f = FuncId::new(3);
        assert_eq!(f.index(), 3);
        assert_eq!(f.as_usize(), 3);
    }

    #[test]
    fn struct_id_construction() {
        let s = StructId::new(1);
        assert_eq!(s.index(), 1);
    }

    #[test]
    fn ty_id_construction() {
        let t = TyId::new(5);
        assert_eq!(t.index(), 5);
    }

    #[test]
    fn func_ty_id_construction() {
        let ft = FuncTyId::new(0);
        assert_eq!(ft.index(), 0);
    }

    #[test]
    fn proof_id_and_tag_construction() {
        let p = ProofId::new(10);
        assert_eq!(p.index(), 10);
        let t = ProofTag::new(99);
        assert_eq!(t.index(), 99);
    }

    #[test]
    fn record_id_construction() {
        let r = RecordId::new(7);
        assert_eq!(r.index(), 7);
        assert_eq!(r.as_usize(), 7);
        assert_eq!(format!("{:?}", r), "RecordId(7)");
        assert_eq!(format!("{}", r), "7");
    }

    #[test]
    fn global_id_construction() {
        let g = GlobalId::new(4);
        assert_eq!(g.index(), 4);
        assert_eq!(g.as_usize(), 4);
        assert_eq!(format!("{g:?}"), "GlobalId(4)");
        assert_eq!(format!("{g}"), "4");
    }

    #[test]
    fn closure_ty_id_construction() {
        let c = ClosureTyId::new(3);
        assert_eq!(c.index(), 3);
        assert_eq!(format!("{:?}", c), "ClosureTyId(3)");
    }

    #[test]
    fn record_and_closure_ids_are_distinct_types() {
        // They share a u32 payload but are distinct Rust types.
        let r = RecordId::new(0);
        let c = ClosureTyId::new(0);
        assert_eq!(r.index(), c.index());
    }

    #[test]
    fn display_outputs_raw_index() {
        assert_eq!(format!("{}", ValueId::new(0)), "0");
        assert_eq!(format!("{}", ValueId::new(123)), "123");
        assert_eq!(format!("{}", BlockId::new(5)), "5");
        assert_eq!(format!("{}", FuncId::new(2)), "2");
    }

    #[test]
    fn debug_includes_type_name() {
        assert_eq!(format!("{:?}", ValueId::new(1)), "ValueId(1)");
        assert_eq!(format!("{:?}", BlockId::new(2)), "BlockId(2)");
        assert_eq!(format!("{:?}", FuncId::new(3)), "FuncId(3)");
    }

    #[test]
    fn ids_are_ordered() {
        assert!(ValueId::new(0) < ValueId::new(1));
        assert!(BlockId::new(5) > BlockId::new(3));
        assert_eq!(FuncId::new(2), FuncId::new(2));
    }

    #[test]
    fn ids_are_copy() {
        let a = ValueId::new(1);
        let b = a; // Copy
        assert_eq!(a, b);
    }

    #[test]
    fn binding_frame_id_construction() {
        let bf = BindingFrameId::new(7);
        assert_eq!(bf.index(), 7);
        assert_eq!(bf.as_usize(), 7);
        assert_eq!(format!("{bf}"), "7");
        assert_eq!(format!("{bf:?}"), "BindingFrameId(7)");
    }

    #[test]
    fn pred_and_univ_id_construction() {
        let p = PredId::new(3);
        assert_eq!(p.index(), 3);
        assert_eq!(p.as_usize(), 3);
        assert_eq!(format!("{p:?}"), "PredId(3)");
        assert_eq!(format!("{p}"), "3");
        let u = UnivId::new(0);
        assert_eq!(u.index(), 0);
        assert_eq!(format!("{u:?}"), "UnivId(0)");
        // Distinct Rust types over the same payload, exactly like
        // RecordId/ClosureTyId above.
        assert_eq!(PredId::new(1).index(), UnivId::new(1).index());
    }

    #[test]
    fn source_span_construction() {
        let span = SourceSpan {
            file: 1,
            line: 42,
            col: 10,
        };
        assert_eq!(span.file, 1);
        assert_eq!(span.line, 42);
        assert_eq!(span.col, 10);
    }
}
