// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Call-free mixed scalar denotation in the existing Nat/Bool vocabulary.
//! This reads actual instructions. It grants no kernel or publication verdict.
use super::*;

const MAX_OPERATIONS: usize = 32;
const MAX_INSTRUCTIONS: usize = 4 * MAX_OPERATIONS + 1;
const MAX_EXPANDED_COST: usize = 65_536;

/// The source carrier and its model image, never a target ABI claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarSort {
    Bool,
    UInt(u32),
}

impl ScalarSort {
    fn from_ir(ty: &Ty) -> Result<Self, ReflectError> {
        if *ty == Ty::Bool {
            return Ok(Self::Bool);
        }
        width_of_ty(ty)
            .map(Self::UInt)
            .ok_or_else(|| unsupported("unsupported scalar carrier"))
    }

    pub fn source_type(self) -> Expr {
        match self {
            Self::Bool => bool_ty(),
            Self::UInt(width) => Expr::const_str(&format!("UInt{width}")),
        }
    }

    pub fn model_type(self) -> Expr {
        match self {
            Self::Bool => bool_ty(),
            Self::UInt(_) => nat(),
        }
    }

    pub fn image(self, value: Expr) -> Expr {
        match self {
            Self::Bool => value,
            Self::UInt(width) => Expr::app(Expr::const_str(&format!("UInt{width}.toNat")), value),
        }
    }
}

/// A computational reading over model-sorted parameter binders. Private fields
/// retain the reader's complete typed result; this object is not proof authority.
#[derive(Debug, Clone)]
pub struct ScalarDenotation {
    parameters: Vec<ScalarSort>,
    result: ScalarSort,
    body: Expr,
}

impl ScalarDenotation {
    pub fn parameters(&self) -> &[ScalarSort] {
        &self.parameters
    }
    pub fn result(&self) -> ScalarSort {
        self.result
    }
    pub fn body(&self) -> &Expr {
        &self.body
    }
}

fn unsupported(reason: &str) -> ReflectError {
    ReflectError::unsupported(format!("typed scalar denotation: {reason}"))
}

struct Value {
    sort: ScalarSort,
    term: Expr,
    dependencies: Vec<u32>,
    cost: usize,
}

fn value(
    values: &BTreeMap<u32, Value>,
    id: ValueId,
    sort: ScalarSort,
) -> Result<&Value, ReflectError> {
    let value = values
        .get(&id.index())
        .ok_or(ReflectError::UnresolvedOperand(id))?;
    if value.sort != sort {
        return Err(unsupported("operand carrier disagrees"));
    }
    Ok(value)
}

fn bool_binary(op: BinOp, a: Expr, b: Expr) -> Result<Expr, ReflectError> {
    let primitive = match op {
        BinOp::BAnd | BinOp::And => "Bool.and",
        BinOp::BOr | BinOp::Or => "Bool.or",
        BinOp::BXor | BinOp::Xor => "Bool.xor",
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::RotL
        | BinOp::RotR
        | BinOp::FCopySign => return Err(unsupported("unsupported Boolean binary operation")),
    };
    Ok(nat_app2(primitive, a, b))
}

fn comparison(op: ICmpOp, sort: ScalarSort, a: Expr, b: Expr) -> Result<Expr, ReflectError> {
    if let ScalarSort::UInt(_) = sort {
        return denote_icmp(op, a, b);
    }
    let different = nat_app2("Bool.xor", a, b);
    match op {
        ICmpOp::Eq => Ok(Expr::app(Expr::const_str("Bool.not"), different)),
        ICmpOp::Ne => Ok(different),
        ICmpOp::Ult
        | ICmpOp::Ule
        | ICmpOp::Ugt
        | ICmpOp::Uge
        | ICmpOp::Slt
        | ICmpOp::Sle
        | ICmpOp::Sgt
        | ICmpOp::Sge => Err(unsupported(
            "ordered Boolean comparison requires its own model",
        )),
    }
}

/// Denote a complete pure single-block Bool/UInt function without uniform-width
/// assumptions. Every value is typed and every definition must reach the return.
/// The original uniform denotation and its callers retain their existing grammar.
pub fn denote_scalar_function(
    module: &Module,
    function: &Function,
) -> Result<ScalarDenotation, ReflectError> {
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| unsupported("missing function signature"))?;
    let [result_ty] = signature.returns.as_slice() else {
        return Err(unsupported("requires exactly one result"));
    };
    if signature.is_vararg || signature.params.len() > 64 {
        return Err(unsupported("vararg or excessive parameter count"));
    }
    let parameters = signature
        .params
        .iter()
        .map(ScalarSort::from_ir)
        .collect::<Result<Vec<_>, _>>()?;
    let result = ScalarSort::from_ir(result_ty)?;
    let [block] = function.blocks.as_slice() else {
        return Err(unsupported("requires exactly one block"));
    };
    if block.id != function.entry
        || block.params.len() != parameters.len()
        || block.body.len() > MAX_INSTRUCTIONS
    {
        return Err(unsupported("entry or instruction budget disagrees"));
    }
    let mut values = BTreeMap::new();
    for (i, ((id, ty), expected)) in block.params.iter().zip(&parameters).enumerate() {
        if ScalarSort::from_ir(ty)? != *expected
            || values
                .insert(
                    id.index(),
                    Value {
                        sort: *expected,
                        term: Expr::bvar((parameters.len() - 1 - i) as u32),
                        dependencies: vec![],
                        cost: 1,
                    },
                )
                .is_some()
        {
            return Err(unsupported("parameter carrier or identity disagrees"));
        }
    }
    let mut definitions = Vec::new();
    let mut operations = 0;
    let mut returned = None;
    for (offset, node) in block.body.iter().enumerate() {
        let (sort, term, dependencies) = match &node.inst {
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(b),
            } => (
                ScalarSort::Bool,
                Expr::const_str(if *b { "Bool.true" } else { "Bool.false" }),
                vec![],
            ),
            Inst::Const {
                ty,
                value: Constant::Int(n),
            } => {
                let sort @ ScalarSort::UInt(width) = ScalarSort::from_ir(ty)? else {
                    return Err(unsupported("integer constant at Bool"));
                };
                if *n < 0 || (*n as u128) >= (1u128 << width) {
                    return Err(unsupported("integer constant outside carrier"));
                }
                (sort, Expr::nat_lit_u128(*n as u128), vec![])
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                operations += 1;
                let sort = ScalarSort::from_ir(ty)?;
                let a = value(&values, *lhs, sort)?.term.clone();
                let b = value(&values, *rhs, sort)?.term.clone();
                let term = match sort {
                    ScalarSort::Bool => bool_binary(*op, a, b)?,
                    ScalarSort::UInt(width) => denote_binop(*op, a, b, &modulus(width))?,
                };
                (sort, term, vec![lhs.index(), rhs.index()])
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                operations += 1;
                let sort = ScalarSort::from_ir(ty)?;
                let a = value(&values, *lhs, sort)?.term.clone();
                let b = value(&values, *rhs, sort)?.term.clone();
                (
                    ScalarSort::Bool,
                    comparison(*op, sort, a, b)?,
                    vec![lhs.index(), rhs.index()],
                )
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                operations += 1;
                let sort = ScalarSort::from_ir(ty)?;
                let condition = value(&values, *cond, ScalarSort::Bool)?.term.clone();
                let yes = value(&values, *then_val, sort)?.term.clone();
                let no = value(&values, *else_val, sort)?.term.clone();
                let term = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [
                        Expr::lam(BinderInfo::Default, bool_ty(), sort.model_type()),
                        no,
                        yes,
                        condition,
                    ],
                );
                (
                    sort,
                    term,
                    vec![cond.index(), then_val.index(), else_val.index()],
                )
            }
            Inst::Return {
                values: returned_values,
            } => {
                let [id] = returned_values.as_slice() else {
                    return Err(unsupported("Return must consume one value"));
                };
                if offset + 1 != block.body.len() || !node.results.is_empty() {
                    return Err(unsupported("Return must be final and define no values"));
                }
                returned = Some((id.index(), value(&values, *id, result)?.term.clone()));
                continue;
            }
            other @ insts!(
                Const,
                UnOp,
                Overflow,
                FCmp,
                Cast,
                Load,
                Store,
                Alloca,
                HeapAlloc,
                GEP,
                PtrData,
                PtrMetadata,
                PtrFromParts,
                AtomicLoad,
                AtomicStore,
                AtomicRMW,
                CmpXchg,
                Fence,
                Br,
                CondBr,
                Switch,
                Call,
                CallIndirect,
                ExtractField,
                InsertField,
                ExtractElement,
                InsertElement,
                NullPtr,
                GlobalAddr,
                Undef,
                Assume,
                Assert,
                Unreachable,
                Copy,
                SeqMapAddK,
                SeqMapNot,
                SeqMap,
                Borrow,
                BorrowMut,
                EndBorrow,
                Retain,
                Release,
                IsUnique,
                Dealloc,
                MemCopy,
                MemSet,
                Drop,
                OpenFrame,
                BindSlot,
                LoadSlot,
                CloseFrame,
                CoroSuspend,
                Invoke,
                InvokeIndirect,
                AssertInvoke,
                CallCannotUnwind,
                CallIndirectCannotUnwind,
                DropInvoke,
                LandingPad,
                Resume,
                DialectOp,
                MakeAggregate,
                ArraySplat,
                MakeClosure,
                TensorContract,
                TensorMap,
                TensorReduce,
                TensorView,
                TensorGather,
                TensorScatter,
            ) => return Err(ReflectError::unsupported(fragment2_inst_label(other))),
        };
        if operations > MAX_OPERATIONS {
            return Err(unsupported("more than 32 scalar operations"));
        }
        let [id] = node.results.as_slice() else {
            return Err(unsupported("definition must produce one value"));
        };
        let cost = dependencies
            .iter()
            .try_fold(16usize, |cost, id| cost.checked_add(values.get(id)?.cost))
            .ok_or_else(|| unsupported("expression cost overflow or undefined dependency"))?;
        if cost > MAX_EXPANDED_COST {
            return Err(unsupported(
                "expanded model exceeds the bounded expression budget",
            ));
        }
        if values
            .insert(
                id.index(),
                Value {
                    sort,
                    term,
                    dependencies,
                    cost,
                },
            )
            .is_some()
        {
            return Err(unsupported("duplicate SSA definition"));
        }
        definitions.push(id.index());
    }
    let (root, body) = returned.ok_or_else(|| unsupported("missing Return"))?;
    let mut live = BTreeSet::from([root]);
    for id in definitions.into_iter().rev() {
        if !live.contains(&id) {
            return Err(unsupported("dead SSA definition"));
        }
        let definition = values
            .get(&id)
            .ok_or_else(|| unsupported("missing definition"))?;
        live.extend(definition.dependencies.iter().copied());
    }
    Ok(ScalarDenotation {
        parameters,
        result,
        body,
    })
}
