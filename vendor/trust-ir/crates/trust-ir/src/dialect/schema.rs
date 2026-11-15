// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Immutable, exact signature and payload grammars for dialect operations.
//!
//! The legacy [`super::DialectRegistry`] combines callbacks and lowering passes.
//! This registry is deliberately data-only: construction rejects ambiguous
//! declarations, and checking cannot be overridden by a dialect callback. A
//! consumer freezes its schemas once and checks operations against their exact
//! versions, operand/result types, and required attribute names and tags.
//!
//! This is **well-formedness, not semantic or proof admission**. An attribute's
//! tag does not prove its value meaningful (a slot must still be in range, for
//! example). Semantic decoders, effect contracts, and independently replayed
//! legalization rules remain necessary. No proof annotation is manufactured or
//! transported here. Unknown dialects may still round-trip through TrustIR, but
//! they cannot pass this opt-in closed registry.

mod observed_lookup;

use super::{AttrValue, DialectInst, NameError, NameRole};
use crate::{FuncTy, FuncTyId, Ty, ValueId};

/// Exact wire tag of a required operation attribute. All declared attributes
/// are required; optional/defaulted payloads need a separately versioned schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttributeKind {
    I64,
    U64,
    F64,
    Bool,
    Str,
    Bytes,
    Ty,
}

impl AttributeKind {
    fn of(value: &AttrValue) -> Self {
        match value {
            AttrValue::I64(_) => Self::I64,
            AttrValue::U64(_) => Self::U64,
            AttrValue::F64(_) => Self::F64,
            AttrValue::Bool(_) => Self::Bool,
            AttrValue::Str(_) => Self::Str,
            AttrValue::Bytes(_) => Self::Bytes,
            AttrValue::Ty(_) => Self::Ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttributeSchema {
    pub name: String,
    pub kind: AttributeKind,
}

/// A module-independent operand contract. Function signatures are structural
/// patterns, not module-relative `FuncTyId`s. They accept only fixed-arity
/// `Ty::Func` values whose module-owned signature matches exactly. A single
/// terminal `VariadicExact` describes zero or more operands of one closed type;
/// it does not permit variadic function signatures or untyped operands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperandType {
    Exact(Ty),
    Function {
        params: Vec<Ty>,
        returns: Vec<Ty>,
    },
    /// Zero or more operands, each having this exact closed type. Valid only
    /// once, at the end of an operation's operand declaration.
    VariadicExact(Ty),
}

impl From<Ty> for OperandType {
    fn from(ty: Ty) -> Self {
        Self::Exact(ty)
    }
}

/// A fixed-prefix operation grammar, optionally followed by one homogeneous
/// variadic tail. Exact types and function pattern members must be closed:
/// scalar, nominal dialect, or inline compositions of closed types, never module-relative
/// `TyId`/aggregate/signature references. A registry must not interpret the same
/// table index as different types in different input modules.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperationSchema {
    pub name: String,
    pub operands: Vec<OperandType>,
    pub results: Vec<Ty>,
    /// Canonically sorted by name when a registry freezes this declaration.
    pub attributes: Vec<AttributeSchema>,
}

impl OperationSchema {
    /// Whether the declaration ends in a zero-minimum homogeneous tail.
    /// The registry separately rejects repeated or nonterminal tails.
    pub fn is_variadic(&self) -> bool {
        matches!(self.operands.last(), Some(OperandType::VariadicExact(_)))
    }

    /// Required prefix length, or the exact operand count for a fixed schema.
    /// This is an O(1) query; use registered schemas for validated layout.
    pub fn minimum_operand_count(&self) -> usize {
        self.operands.len() - usize::from(self.is_variadic())
    }

    /// Check the count without expanding a variadic declaration into a list.
    /// This query does not validate an unregistered declaration's layout.
    pub fn accepts_operand_count(&self, actual: usize) -> bool {
        let minimum = self.minimum_operand_count();
        actual == minimum || (self.is_variadic() && actual > minimum)
    }

    /// Borrow the contract for an absolute operand index. A terminal variadic
    /// contract is shared by every tail index; fixed schemas return `None`
    /// beyond their last operand. The registry validates declaration layout.
    pub fn operand_type_at(&self, index: usize) -> Option<&OperandType> {
        self.operands.get(index).or_else(|| {
            self.operands
                .last()
                .filter(|operand| matches!(operand, OperandType::VariadicExact(_)))
        })
    }

    fn validate_operand_count(&self, actual: usize) -> Result<(), SchemaError> {
        if self.accepts_operand_count(actual) {
            Ok(())
        } else if self.is_variadic() {
            Err(SchemaError::OperandCountAtLeast {
                minimum: self.minimum_operand_count(),
                actual,
            })
        } else {
            Err(SchemaError::OperandCount {
                expected: self.minimum_operand_count(),
                actual,
            })
        }
    }

    fn validate_variadic_layout(&self) -> Result<(), SchemaError> {
        let mut first = None;
        for (index, operand) in self.operands.iter().enumerate() {
            if matches!(operand, OperandType::VariadicExact(_)) {
                if let Some(first) = first {
                    return Err(SchemaError::RepeatedVariadicOperand {
                        first,
                        repeated: index,
                    });
                }
                first = Some(index);
            }
        }
        if let Some(index) = first
            && index != self.operands.len() - 1
        {
            return Err(SchemaError::NonTerminalVariadicOperand { index });
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DialectSchema {
    pub namespace: String,
    pub version: u32,
    pub operations: Vec<OperationSchema>,
}

/// Frozen declarations. There is no mutation API after construction, no
/// registration-order override, and no lowering callback hidden in the schema.
#[derive(Debug)]
pub struct DialectSchemaRegistry {
    // Frozen sorted slices are their own indexes. Each declaration name is
    // retained once, not duplicated into a separate map key.
    dialects: Vec<DialectSchema>,
}

/// Attribute ordinals fit in one stack word for ordinary operation schemas.
/// Unusually wide schemas remain supported with proportionate bit storage.
enum SeenAttributes {
    Inline(u64),
    Wide(Vec<u64>),
}

impl SeenAttributes {
    fn new(count: usize) -> Self {
        if count <= 64 {
            Self::Inline(0)
        } else {
            Self::Wide(vec![0; count.div_ceil(64)])
        }
    }

    fn contains(&self, index: usize) -> bool {
        let word = match self {
            Self::Inline(word) => *word,
            Self::Wide(words) => words[index / 64],
        };
        word & (1 << (index % 64)) != 0
    }

    fn insert(&mut self, index: usize) -> bool {
        let word = match self {
            Self::Inline(word) => word,
            Self::Wide(words) => &mut words[index / 64],
        };
        let mask = 1 << (index % 64);
        let fresh = *word & mask == 0;
        *word |= mask;
        fresh
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaError {
    InvalidName(NameError),
    ZeroVersion,
    DuplicateDialect(String),
    DuplicateOperation(String),
    DuplicateAttribute(String),
    NonClosedType(Ty),
    UnknownDialect(String),
    VersionMismatch {
        expected: u32,
        actual: u32,
    },
    UnknownOperation(String),
    OperandCount {
        expected: usize,
        actual: usize,
    },
    /// A variadic operation is missing required fixed-prefix operands.
    OperandCountAtLeast {
        minimum: usize,
        actual: usize,
    },
    /// A declaration contains more than one variadic tail.
    RepeatedVariadicOperand {
        first: usize,
        repeated: usize,
    },
    /// A variadic tail is followed by another operand declaration.
    NonTerminalVariadicOperand {
        index: usize,
    },
    UndefinedOperand(ValueId),
    OperandType {
        index: usize,
        expected: Ty,
        actual: Ty,
    },
    ExpectedFunctionOperand {
        index: usize,
        actual: Ty,
    },
    FunctionTypeUnavailable {
        index: usize,
        signature: FuncTyId,
    },
    /// Full signatures are retained only on the cold mismatch path. Indirection
    /// keeps successful schema-check results from carrying their large layout.
    FunctionSignature {
        index: usize,
        expected: Box<FuncTy>,
        actual: Box<FuncTy>,
    },
    ResultTypes,
    ResultCount {
        expected: usize,
        actual: usize,
    },
    UnknownAttribute(String),
    MissingAttribute(String),
    AttributeType {
        name: String,
        expected: AttributeKind,
        actual: AttributeKind,
    },
}

impl core::fmt::Display for SchemaError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "dialect schema mismatch: {self:?}")
    }
}

impl std::error::Error for SchemaError {}

fn check_name(name: &str, role: NameRole) -> Result<(), SchemaError> {
    if name.is_empty() || !name.chars().all(super::inst::is_valid_dialect_name_char) {
        return Err(SchemaError::InvalidName(NameError {
            role,
            name: name.into(),
        }));
    }
    Ok(())
}

fn is_closed_type(ty: &Ty) -> bool {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        match ty {
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never => {}
            Ty::Dialect(ty) if ty.validate().is_ok() => {}
            // v43 handles are pinned to a runtime by the validator, never by
            // an op schema: a schema that produced or consumed one would be a
            // second, unpinned origin. Refused here; the fallthrough below
            // makes that explicit rather than incidental.
            Ty::Handle(_) => return false,
            Ty::Tuple(types) => pending.extend(types),
            Ty::Vector(elem, lanes) if *lanes > 0 => pending.push(elem),
            Ty::Ref(elem)
            | Ty::RefMut(elem)
            | Ty::PtrConst(elem)
            | Ty::PtrMut(elem)
            | Ty::Rc(elem) => pending.push(elem),
            // Closed fixed signatures only. Do not treat an unknown/new type
            // or a module-relative reference as a globally meaningful schema.
            _ => return false,
        }
    }
    true
}

impl DialectSchemaRegistry {
    /// Freeze a set of exact schemas. Duplicate namespaces are rejected even
    /// if their versions or complete declarations agree. A failed construction
    /// publishes no partially registered lookup/pass state.
    pub fn new(schemas: impl IntoIterator<Item = DialectSchema>) -> Result<Self, SchemaError> {
        let mut dialects = schemas.into_iter().collect::<Vec<_>>();
        dialects.sort_unstable_by(|a, b| a.namespace.cmp(&b.namespace));
        for pair in dialects.windows(2) {
            if pair[0].namespace == pair[1].namespace {
                return Err(SchemaError::DuplicateDialect(pair[1].namespace.clone()));
            }
        }
        for schema in &mut dialects {
            check_name(&schema.namespace, NameRole::Dialect)?;
            if schema.version == 0 {
                return Err(SchemaError::ZeroVersion);
            }
            schema
                .operations
                .sort_unstable_by(|a, b| a.name.cmp(&b.name));
            for pair in schema.operations.windows(2) {
                if pair[0].name == pair[1].name {
                    return Err(SchemaError::DuplicateOperation(pair[1].name.clone()));
                }
            }
            for op in &mut schema.operations {
                check_name(&op.name, NameRole::Op)?;
                op.validate_variadic_layout()?;
                for ty in op
                    .operands
                    .iter()
                    .flat_map(|operand| match operand {
                        OperandType::Exact(ty) | OperandType::VariadicExact(ty) => {
                            std::slice::from_ref(ty).iter().chain([].iter())
                        }
                        OperandType::Function { params, returns } => params.iter().chain(returns),
                    })
                    .chain(&op.results)
                {
                    if !is_closed_type(ty) {
                        return Err(SchemaError::NonClosedType(ty.clone()));
                    }
                }
                op.attributes.sort_unstable_by(|a, b| a.name.cmp(&b.name));
                for pair in op.attributes.windows(2) {
                    if pair[0].name == pair[1].name {
                        return Err(SchemaError::DuplicateAttribute(pair[1].name.clone()));
                    }
                }
                for attr in &op.attributes {
                    check_name(&attr.name, NameRole::Attr)?;
                }
            }
        }
        Ok(Self { dialects })
    }

    /// Check an operation against the frozen grammar without cloning the
    /// operation or its successful type lookups. `type_of` must read actual SSA
    /// definitions in the containing module, not producer-supplied claims.
    /// The enclosing module validator remains responsible for SSA dominance,
    /// duplicate definitions, and legality of non-dialect instructions.
    ///
    /// Returns the borrowed declaration for a subsequent semantic decoder. It
    /// is not a checked-module owner or a semantic/proof certificate.
    pub fn validate_op<'registry, 'ty>(
        &'registry self,
        op: &DialectInst,
        result_count: usize,
        type_of: impl Fn(ValueId) -> Option<&'ty Ty>,
    ) -> Result<&'registry OperationSchema, SchemaError> {
        self.validate_op_with_func_types(op, result_count, type_of, |_| None)
    }

    /// Check actual SSA operands and resolve function signatures in the same
    /// containing module. Neither callback is evidence: authoritative module
    /// validation supplies both from its existing owned tables/type inventory.
    ///
    /// The legacy [`Self::validate_op`] remains sufficient for exact-only
    /// schemas and fails closed on function operands requiring this context.
    /// This checks a function *type*, not callback behavior, calling convention,
    /// capture correspondence, or semantic authority. General constant/module
    /// validation must separately check `Constant::FnDef` target identities.
    pub fn validate_op_with_func_types<'registry, 'ty, 'signature>(
        &'registry self,
        op: &DialectInst,
        result_count: usize,
        type_of: impl Fn(ValueId) -> Option<&'ty Ty>,
        func_type_of: impl Fn(FuncTyId) -> Option<&'signature FuncTy>,
    ) -> Result<&'registry OperationSchema, SchemaError> {
        op.validate_names().map_err(SchemaError::InvalidName)?;
        let dialect_index = self
            .dialects
            .binary_search_by(|schema| schema.namespace.cmp(&op.dialect))
            .map_err(|_| SchemaError::UnknownDialect(op.dialect.clone()))?;
        let dialect = &self.dialects[dialect_index];
        if op.version != dialect.version {
            return Err(SchemaError::VersionMismatch {
                expected: dialect.version,
                actual: op.version,
            });
        }
        let op_index = dialect
            .operations
            .binary_search_by(|schema| schema.name.cmp(&op.op))
            .map_err(|_| SchemaError::UnknownOperation(op.op.clone()))?;
        let schema = &dialect.operations[op_index];
        schema.validate_operand_count(op.operands.len())?;
        if op.result_tys != schema.results {
            return Err(SchemaError::ResultTypes);
        }
        if result_count != schema.results.len() {
            return Err(SchemaError::ResultCount {
                expected: schema.results.len(),
                actual: result_count,
            });
        }
        for (index, id) in op.operands.iter().enumerate() {
            let expected = schema
                .operand_type_at(index)
                .expect("validated count and registered operand layout");
            let actual = type_of(*id).ok_or(SchemaError::UndefinedOperand(*id))?;
            match expected {
                OperandType::Exact(expected) | OperandType::VariadicExact(expected)
                    if actual != expected =>
                {
                    return Err(SchemaError::OperandType {
                        index,
                        expected: expected.clone(),
                        actual: actual.clone(),
                    });
                }
                OperandType::Exact(_) | OperandType::VariadicExact(_) => {}
                OperandType::Function { params, returns } => {
                    let Ty::Func(signature) = actual else {
                        return Err(SchemaError::ExpectedFunctionOperand {
                            index,
                            actual: actual.clone(),
                        });
                    };
                    let actual =
                        func_type_of(*signature).ok_or(SchemaError::FunctionTypeUnavailable {
                            index,
                            signature: *signature,
                        })?;
                    if actual.is_vararg || actual.params != *params || actual.returns != *returns {
                        return Err(SchemaError::FunctionSignature {
                            index,
                            expected: Box::new(FuncTy {
                                params: params.clone(),
                                returns: returns.clone(),
                                abi: None,
                                is_vararg: false,
                            }),
                            actual: Box::new(actual.clone()),
                        });
                    }
                }
            }
        }
        let mut seen = SeenAttributes::new(schema.attributes.len());
        for attr in &op.attrs {
            let index = schema
                .attributes
                .binary_search_by(|schema| schema.name.cmp(&attr.name))
                .map_err(|_| SchemaError::UnknownAttribute(attr.name.clone()))?;
            let expected = schema.attributes[index].kind;
            if !seen.insert(index) {
                return Err(SchemaError::DuplicateAttribute(attr.name.clone()));
            }
            let actual = AttributeKind::of(&attr.value);
            if expected != actual {
                return Err(SchemaError::AttributeType {
                    name: attr.name.clone(),
                    expected,
                    actual,
                });
            }
        }
        if op.attrs.len() != schema.attributes.len() {
            let (_, attr) = schema
                .attributes
                .iter()
                .enumerate()
                .find(|(index, _)| !seen.contains(*index))
                .unwrap();
            return Err(SchemaError::MissingAttribute(attr.name.clone()));
        }
        Ok(schema)
    }
}

#[cfg(test)]
#[path = "schema/variadic_tests.rs"]
mod variadic_tests;

#[cfg(test)]
#[path = "schema/error_payload_tests.rs"]
mod error_payload_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::DialectTy;

    fn value_ty() -> Ty {
        Ty::Dialect(Box::new(DialectTy {
            namespace: "example".into(),
            name: "value".into(),
            version: 1,
        }))
    }

    fn schema() -> DialectSchema {
        DialectSchema {
            namespace: "example".into(),
            version: 1,
            operations: vec![OperationSchema {
                name: "read".into(),
                operands: vec![value_ty().into()],
                results: vec![value_ty()],
                attributes: vec![AttributeSchema {
                    name: "slot".into(),
                    kind: AttributeKind::U64,
                }],
            }],
        }
    }

    fn op() -> DialectInst {
        DialectInst::new("example", "read")
            .with_operand(ValueId::new(2))
            .with_result_ty(value_ty())
            .with_attr("slot", AttrValue::U64(7))
    }

    #[test]
    fn closed_registry_checks_nominal_signature_and_returns_borrowed_schema() {
        let registry = DialectSchemaRegistry::new([schema()]).unwrap();
        let ty = value_ty();
        let lookup = |id| (id == ValueId::new(2)).then_some(&ty);
        let checked = registry.validate_op(&op(), 1, lookup).unwrap();
        let checked_again = registry.validate_op(&op(), 1, lookup).unwrap();
        assert!(std::ptr::eq(checked, checked_again));
        assert_eq!(checked.name, "read");
    }

    fn callback_registry() -> DialectSchemaRegistry {
        let mut declaration = schema();
        declaration.operations[0].operands[0] = OperandType::Function {
            params: vec![value_ty()],
            returns: vec![value_ty(), Ty::Bool],
        };
        DialectSchemaRegistry::new([declaration]).unwrap()
    }

    #[test]
    fn function_patterns_resolve_owned_signatures_without_baking_in_table_ids() {
        let registry = callback_registry();
        let signature = FuncTy {
            params: vec![value_ty()],
            returns: vec![value_ty(), Ty::Bool],
            abi: None,
            is_vararg: false,
        };
        // One immutable registry works for independent modules whose matching
        // signature occupies a different table slot.
        for ordinal in [0, 91] {
            let id = FuncTyId::new(ordinal);
            let ty = Ty::Func(id);
            assert!(
                registry
                    .validate_op_with_func_types(
                        &op(),
                        1,
                        |_| Some(&ty),
                        |actual| (actual == id).then_some(&signature)
                    )
                    .is_ok()
            );
            assert!(matches!(registry.validate_op(&op(), 1, |_| Some(&ty)),
                Err(SchemaError::FunctionTypeUnavailable { signature, .. }) if signature == id));
        }
    }

    #[test]
    fn function_patterns_reject_missing_wrong_and_variadic_signatures() {
        let registry = callback_registry();
        let ty = Ty::Func(FuncTyId::new(7));
        let valid = FuncTy {
            params: vec![value_ty()],
            returns: vec![value_ty(), Ty::Bool],
            abi: None,
            is_vararg: false,
        };
        for kind in 0..5 {
            let mut bad = valid.clone();
            match kind {
                0 => bad.params.clear(),
                1 => bad.params[0] = Ty::I64,
                2 => bad.returns.reverse(),
                3 => bad.returns.pop().map(drop).unwrap(),
                _ => bad.is_vararg = true,
            }
            assert!(matches!(
                registry.validate_op_with_func_types(&op(), 1, |_| Some(&ty), |_| Some(&bad)),
                Err(SchemaError::FunctionSignature { .. })
            ));
        }
        for ty in [Ty::Ptr, Ty::I64, value_ty()] {
            assert!(matches!(
                registry.validate_op_with_func_types(&op(), 1, |_| Some(&ty), |_| Some(&valid)),
                Err(SchemaError::ExpectedFunctionOperand { .. })
            ));
        }
        assert!(matches!(
            registry.validate_op_with_func_types(&op(), 1, |_| Some(&ty), |_| None),
            Err(SchemaError::FunctionTypeUnavailable { .. })
        ));
    }

    #[test]
    fn function_pattern_members_must_be_closed_and_nominally_well_formed() {
        for ty in [
            Ty::Func(FuncTyId::new(0)),
            Ty::Tuple(vec![Ty::Struct(crate::StructId::new(0))]),
            Ty::Dialect(Box::new(DialectTy::new("invalid.name", "value", 1))),
        ] {
            for in_result in [false, true] {
                let mut declaration = schema();
                declaration.operations[0].operands[0] = OperandType::Function {
                    params: if in_result { vec![] } else { vec![ty.clone()] },
                    returns: if in_result { vec![ty.clone()] } else { vec![] },
                };
                assert!(matches!(
                    DialectSchemaRegistry::new([declaration]),
                    Err(SchemaError::NonClosedType(_))
                ));
            }
        }
    }

    #[test]
    fn registration_rejects_duplicates_and_non_closed_type_ids() {
        assert_eq!(
            DialectSchemaRegistry::new([schema(), schema()]).unwrap_err(),
            SchemaError::DuplicateDialect("example".into())
        );
        let mut duplicate = schema();
        duplicate.operations.push(duplicate.operations[0].clone());
        assert_eq!(
            DialectSchemaRegistry::new([duplicate]).unwrap_err(),
            SchemaError::DuplicateOperation("read".into())
        );
        let mut duplicate = schema();
        duplicate.operations[0].attributes.push(AttributeSchema {
            name: "slot".into(),
            kind: AttributeKind::U64,
        });
        assert_eq!(
            DialectSchemaRegistry::new([duplicate]).unwrap_err(),
            SchemaError::DuplicateAttribute("slot".into())
        );
        let mut bad = schema();
        bad.operations[0].operands[0] = Ty::Struct(crate::StructId::new(0)).into();
        assert!(matches!(
            DialectSchemaRegistry::new([bad]),
            Err(SchemaError::NonClosedType(_))
        ));
    }

    #[test]
    fn registration_rejects_malformed_names_versions_and_nominal_types() {
        let mut bad = schema();
        bad.version = 0;
        assert_eq!(
            DialectSchemaRegistry::new([bad]).unwrap_err(),
            SchemaError::ZeroVersion
        );
        for role in 0..3 {
            let mut bad = schema();
            match role {
                0 => bad.namespace = "has.dot".into(),
                1 => bad.operations[0].name.clear(),
                _ => bad.operations[0].attributes[0].name = "space name".into(),
            }
            assert!(matches!(
                DialectSchemaRegistry::new([bad]),
                Err(SchemaError::InvalidName(_))
            ));
        }
        let mut bad = schema();
        bad.operations[0].results[0] = Ty::Dialect(Box::new(DialectTy {
            namespace: "example".into(),
            name: "value".into(),
            version: 0,
        }));
        assert!(matches!(
            DialectSchemaRegistry::new([bad]),
            Err(SchemaError::NonClosedType(_))
        ));
    }

    #[test]
    fn lookup_rejects_unknown_names_and_versions_without_callback_override() {
        let registry = DialectSchemaRegistry::new([schema()]).unwrap();
        let ty = value_ty();
        let mut bad = op();
        bad.version = 2;
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::VersionMismatch {
                expected: 1,
                actual: 2
            }
        );
        bad = op();
        bad.op = "unknown".into();
        assert!(matches!(
            registry.validate_op(&bad, 1, |_| Some(&ty)),
            Err(SchemaError::UnknownOperation(_))
        ));
        bad = op();
        bad.dialect = "unknown".into();
        assert!(matches!(
            registry.validate_op(&bad, 1, |_| Some(&ty)),
            Err(SchemaError::UnknownDialect(_))
        ));
    }

    #[test]
    fn operands_are_resolved_and_compared_by_exact_nominal_identity() {
        let registry = DialectSchemaRegistry::new([schema()]).unwrap();
        assert_eq!(
            registry.validate_op(&op(), 1, |_| None).unwrap_err(),
            SchemaError::UndefinedOperand(ValueId::new(2))
        );
        for actual in [
            Ty::I64,
            Ty::Ptr,
            Ty::Dialect(Box::new(DialectTy {
                namespace: "other".into(),
                name: "value".into(),
                version: 1,
            })),
            Ty::Dialect(Box::new(DialectTy {
                namespace: "example".into(),
                name: "other".into(),
                version: 1,
            })),
            Ty::Dialect(Box::new(DialectTy {
                namespace: "example".into(),
                name: "value".into(),
                version: 2,
            })),
        ] {
            assert!(matches!(
                registry.validate_op(&op(), 1, |_| Some(&actual)),
                Err(SchemaError::OperandType { .. })
            ));
        }
        let mut bad = op();
        bad.operands.clear();
        assert!(matches!(
            registry.validate_op(&bad, 1, |_| None),
            Err(SchemaError::OperandCount { .. })
        ));
    }

    #[test]
    fn results_check_both_payload_types_and_enclosing_node_arity() {
        let registry = DialectSchemaRegistry::new([schema()]).unwrap();
        let ty = value_ty();
        let mut bad = op();
        bad.result_tys[0] = Ty::I64;
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::ResultTypes
        );
        assert_eq!(
            registry.validate_op(&op(), 0, |_| Some(&ty)).unwrap_err(),
            SchemaError::ResultCount {
                expected: 1,
                actual: 0
            }
        );
    }

    #[test]
    fn attributes_are_required_unique_exactly_named_and_exactly_tagged() {
        let registry = DialectSchemaRegistry::new([schema()]).unwrap();
        let ty = value_ty();
        let mut bad = op();
        bad.attrs.clear();
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::MissingAttribute("slot".into())
        );
        bad = op().with_attr("slot", AttrValue::U64(7));
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::DuplicateAttribute("slot".into())
        );
        bad = op().with_attr("ignored", AttrValue::Bool(true));
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::UnknownAttribute("ignored".into())
        );
        bad = op();
        bad.attrs[0].value = AttrValue::I64(7);
        assert_eq!(
            registry.validate_op(&bad, 1, |_| Some(&ty)).unwrap_err(),
            SchemaError::AttributeType {
                name: "slot".into(),
                expected: AttributeKind::U64,
                actual: AttributeKind::I64,
            }
        );
    }

    #[test]
    fn wide_attribute_schemas_check_every_ordinal_in_arbitrary_payload_order() {
        for count in [0, 1, 64, 65, 129] {
            let mut declaration = schema();
            declaration.operations[0].attributes = (0..count)
                .rev()
                .map(|index| AttributeSchema {
                    name: format!("attr_{index:03}"),
                    kind: AttributeKind::U64,
                })
                .collect();
            let retained_name = declaration.operations[0].name.as_ptr();
            let registry = DialectSchemaRegistry::new([declaration]).unwrap();
            let ty = value_ty();
            let mut operation = op();
            operation.attrs = (0..count)
                .rev()
                .map(|index| super::super::AttrEntry {
                    name: format!("attr_{index:03}"),
                    value: AttrValue::U64(index),
                })
                .collect();
            let checked = registry.validate_op(&operation, 1, |_| Some(&ty)).unwrap();
            assert_eq!(
                checked.name.as_ptr(),
                retained_name,
                "freeze retains the original name allocation"
            );
            assert!(
                checked
                    .attributes
                    .windows(2)
                    .all(|pair| pair[0].name < pair[1].name)
            );
            if count > 0 {
                operation.attrs.push(operation.attrs[0].clone());
                assert!(matches!(
                    registry.validate_op(&operation, 1, |_| Some(&ty)),
                    Err(SchemaError::DuplicateAttribute(_))
                ));
                operation.attrs.pop();
                let missing = operation.attrs.remove(0).name;
                assert_eq!(
                    registry
                        .validate_op(&operation, 1, |_| Some(&ty))
                        .unwrap_err(),
                    SchemaError::MissingAttribute(missing)
                );
            }
        }
    }

    #[test]
    fn common_attribute_tracking_is_inline_and_wide_tracking_is_exact() {
        assert!(matches!(SeenAttributes::new(0), SeenAttributes::Inline(0)));
        assert!(matches!(SeenAttributes::new(64), SeenAttributes::Inline(0)));
        for count in [1, 64, 65, 128, 129] {
            let mut seen = SeenAttributes::new(count);
            for index in (0..count).rev() {
                assert!(!seen.contains(index));
                assert!(seen.insert(index));
                assert!(seen.contains(index));
                assert!(!seen.insert(index));
            }
        }
    }
}
