// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! ABI claims attached to the type of a callable, including an arbitrary
//! function pointer. These describe the producer's target ABI; they confer no
//! proof authority. A consumer must check the claims against its own lowering.
//!
//! Source modes and emitted carriers are separate. `arguments` retains every
//! source argument, including ignored arguments; `bindings` identifies exactly
//! which lowered parameters or results carry each source value. Padding in a
//! register is distinct from the source bytes that it transports.
//!
//! A consumer must refuse contradictory source/carrier census, target facts,
//! or legacy function attributes; the corpus rows are
//! `refuse/signature_abi_duplicate_binding`,
//! `refuse/signature_abi_target_disagreement`, and
//! `refuse/signature_abi_function_attribute_disagreement`.
//! Unknown descriptor syntax must be refused by the reader:
//! `refuse/signature_abi_unknown_field`. These are test-rung obligations;
//! recorded ABI claims confer no semantic or proof authority.

use crate::ty::FuncTy;

mod observed_validation;
mod text;
pub use text::{AbiTextError, MAX_ABI_TEXT_BYTES};

// A present descriptor records explicit absence as null. Serde's ordinary
// Option field rule otherwise silently accepts an omitted source fact.
#[cfg(feature = "serde")]
fn required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: serde::Deserialize<'de>,
{
    serde::Deserialize::deserialize(deserializer)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct SignatureAbi {
    pub target: AbiTarget,
    /// Exact producer identity, not a promise that this producer is trusted.
    pub frontend: AbiFrontend,
    /// The producer's canonical convention name, distinct from a source ABI
    /// spelling such as Rust/rust-call that can select the same convention.
    pub convention: String,
    /// Convention used by the lowered IR call instruction. A backend checks
    /// that its carrier mapping implements the producer convention above.
    pub lowered_convention: crate::CallingConv,
    pub source_abi: String,
    pub can_unwind: bool,
    pub variadic: bool,
    pub fixed_count: u32,
    pub arguments: Vec<AbiArgument>,
    pub result: AbiArgument,
}

/// Borrowed reconciliation of source placement evidence with the canonical
/// lowered signature and function attributes. This establishes structural
/// agreement only; it does not prove any target ABI or emitted machine code.
///
/// The fields are private so a consumer cannot create a checked view by
/// pairing unrelated claims. The ordinary `FuncTy::abi` data remains an
/// untrusted producer record until these checks (and the consumer's physical
/// ABI checks) succeed.
pub struct FnAbiView<'a> {
    placement: &'a SignatureAbi,
    signature: &'a FuncTy,
    function: &'a crate::Function,
}

impl<'a> FnAbiView<'a> {
    pub fn placement(&self) -> &'a SignatureAbi {
        self.placement
    }

    /// Uses the signature's canonical variadic fact, after checking the
    /// producer's source census against it.
    pub fn is_vararg(&self) -> bool {
        self.signature.is_vararg
    }

    pub fn calling_convention(&self) -> crate::CallingConv {
        self.function.calling_conv
    }

    pub fn parameter_attributes(&self) -> &'a [crate::ParamAttrs] {
        &self.function.attrs.params
    }

    pub fn return_attributes(&self) -> &'a crate::ParamAttrs {
        &self.function.attrs.ret
    }
}

impl crate::Function {
    /// Derive a view without adding a second stored function-level ABI.
    /// Legacy absence remains unrecorded. A contradictory descriptor,
    /// signature, target or lowered slot fact is an error.
    pub fn fn_abi<'a>(
        &'a self,
        module: &'a crate::Module,
    ) -> Result<Option<FnAbiView<'a>>, String> {
        let signature = module
            .func_type(self.ty)
            .ok_or("function signature is out of range")?;
        let Some(placement) = &signature.abi else {
            return Ok(None);
        };
        placement.validate(signature)?;
        placement.validate_target(module.target_info.as_ref())?;
        placement.reconcile_function(self)?;
        Ok(Some(FnAbiView {
            placement,
            signature,
            function: self,
        }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiTarget {
    pub triple: String,
    pub data_layout: String,
    pub abi: String,
    pub cpu: String,
    /// Canonical resolved target features, sorted and unique.
    pub features: Vec<String>,
    /// Producer digest of its complete target specification; an identity claim.
    pub target_spec: String,
    pub pointer_bytes: u8,
    pub little_endian: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiFrontend {
    pub name: String,
    pub revision: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiArgument {
    /// Allocated source storage, including tail padding. This is not a sum of
    /// register widths, and does not claim that padding is initialized.
    pub size: u64,
    pub align: u64,
    pub mode: AbiPassMode,
    pub bindings: Vec<AbiBinding>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum AbiBindingPlace {
    Parameter(u32),
    Result(u32),
    /// The result buffer occupies this lowered parameter. It is not an
    /// ordinary source argument and must not consume an AArch64 x0..x7 slot.
    HiddenResult(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiBinding {
    pub place: AbiBindingPlace,
    pub source_offset: u64,
    /// Source extent represented by this lowered value. For an indirect
    /// binding this is the pointee extent, not the pointer width.
    pub source_bytes: u64,
    /// Byte range within the lowered IR value. Distinct source arguments may
    /// occupy disjoint ranges of a tuple carrier. Indirect bindings record
    /// pointer width here and pointee extent in `source_bytes`.
    pub carrier_offset: u64,
    pub carrier_bytes: u64,
}

/// Explicitly recorded extension. An absent `FuncTy::abi` is unrecorded;
/// `None` here is the producer's positive claim that no extension is required.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum AbiExtension {
    None,
    Sign,
    Zero,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum AbiCapture {
    Any,
    ReadOnly,
    Address,
    None,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiAttributes {
    pub extension: AbiExtension,
    pub in_reg: bool,
    pub no_alias: bool,
    pub nonnull: bool,
    pub readonly: bool,
    pub no_undef: bool,
    pub writable: bool,
    pub no_free: bool,
    pub capture: AbiCapture,
    pub pointee_size: u64,
    #[cfg_attr(feature = "serde", serde(deserialize_with = "required_option"))]
    pub pointee_align: Option<u64>,
}

impl Default for AbiAttributes {
    fn default() -> Self {
        Self {
            extension: AbiExtension::None,
            in_reg: false,
            no_alias: false,
            nonnull: false,
            readonly: false,
            no_undef: false,
            writable: false,
            no_free: false,
            capture: AbiCapture::Any,
            pointee_size: 0,
            pointee_align: None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum AbiRegisterClass {
    Integer,
    Float,
    Vector,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiRegister {
    pub class: AbiRegisterClass,
    pub bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiScalar {
    pub register: AbiRegister,
    pub source_offset: u64,
    pub source_bytes: u64,
    /// Defined value bits; a Boolean has one bit in a one-byte storage lane.
    pub value_bits: u16,
    pub attributes: AbiAttributes,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct AbiUniform {
    pub unit: AbiRegister,
    /// Live extent. The final integer carrier may contain additional padding.
    pub total: u64,
    /// An indivisible register/stack allocation group.
    pub consecutive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum AbiPassMode {
    Ignore,
    Direct(AbiScalar),
    Pair(AbiScalar, AbiScalar),
    Cast {
        pad_i32: bool,
        prefix: Vec<AbiRegister>,
        #[cfg_attr(feature = "serde", serde(deserialize_with = "required_option"))]
        rest_offset: Option<u64>,
        rest: AbiUniform,
        attributes: AbiAttributes,
    },
    Indirect {
        attributes: AbiAttributes,
        #[cfg_attr(feature = "serde", serde(deserialize_with = "required_option"))]
        metadata_attributes: Option<AbiAttributes>,
        on_stack: bool,
        /// Whether a distinct writable caller copy is required. A source
        /// reference carried as a scalar pointer never uses this mode.
        caller_copy: bool,
    },
}

/// Structural consistency only. This does not classify any target ABI and
/// does not certify that an emitted call implements the descriptor.
impl SignatureAbi {
    pub fn to_canonical_text(&self) -> String {
        text::encode(self)
    }

    pub fn from_canonical_text(text: &str) -> Result<Self, AbiTextError> {
        text::decode(text)
    }

    /// Resource bounds shared by fallible writers and the bounded reader.
    /// This checks encoding capacity, not whether the ABI claims are true.
    pub fn validate_encoding_limits(&self) -> Result<(), String> {
        let identities = [
            &self.target.triple,
            &self.target.data_layout,
            &self.target.abi,
            &self.target.cpu,
            &self.target.target_spec,
            &self.frontend.name,
            &self.frontend.revision,
            &self.convention,
            &self.source_abi,
        ];
        let mut bytes = 0usize;
        for text in identities.into_iter().chain(self.target.features.iter()) {
            bytes = bytes
                .checked_add(text.len())
                .ok_or("ABI identity byte count overflows")?;
            if bytes > MAX_ABI_TEXT_BYTES {
                return Err("ABI identity exceeds wire byte limit".into());
            }
        }
        text::validate_node_budget(self)?;
        Self::from_canonical_text(&self.to_canonical_text())
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    pub fn validate(&self, signature: &FuncTy) -> Result<(), String> {
        self.validate_encoding_limits()?;
        if self.target.triple.is_empty()
            || self.target.data_layout.is_empty()
            || self.target.cpu.is_empty()
            || self.target.target_spec.is_empty()
            || self.frontend.name.is_empty()
            || self.frontend.revision.is_empty()
            || self.convention.is_empty()
            || self.source_abi.is_empty()
        {
            return Err("signature ABI identity is incomplete".into());
        }
        if self.target.features.iter().any(|f| f.is_empty())
            || self.target.features.windows(2).any(|w| w[0] >= w[1])
        {
            return Err("target features are not sorted, unique, nonempty names".into());
        }
        if !matches!(self.target.pointer_bytes, 2 | 4 | 8 | 16) {
            return Err("signature ABI pointer width is invalid".into());
        }
        if self.variadic != signature.is_vararg || self.fixed_count as usize > self.arguments.len()
        {
            return Err("signature ABI variadic/fixed argument census disagrees".into());
        }
        let mut parameters = vec![Vec::new(); signature.params.len()];
        let mut results = vec![Vec::new(); signature.returns.len()];
        for (index, arg) in self.arguments.iter().enumerate() {
            validate_argument(arg, false)
                .map_err(|detail| format!("source argument {index}: {detail}"))?;
            for binding in &arg.bindings {
                let AbiBindingPlace::Parameter(index) = binding.place else {
                    return Err("source argument has a result or hidden-result binding".into());
                };
                if matches!(
                    arg.mode,
                    AbiPassMode::Indirect {
                        metadata_attributes: None,
                        on_stack: false,
                        ..
                    }
                ) && (signature.params.get(index as usize) != Some(&crate::Ty::Ptr)
                    || binding.carrier_offset != 0
                    || binding.carrier_bytes != u64::from(self.target.pointer_bytes))
                {
                    return Err("indirect argument does not name one prelowered Ptr carrier".into());
                }
                claim(&mut parameters, index, binding, "parameter")?;
            }
        }
        validate_argument(&self.result, true).map_err(|s| format!("source result: {s}"))?;
        for binding in &self.result.bindings {
            match binding.place {
                AbiBindingPlace::Result(index) => claim(&mut results, index, binding, "result")?,
                AbiBindingPlace::HiddenResult(index) => {
                    if !matches!(
                        self.result.mode,
                        AbiPassMode::Indirect {
                            on_stack: false,
                            ..
                        }
                    ) || !signature.returns.is_empty()
                        || self.result.bindings.len() != 1
                    {
                        return Err(
                            "hidden result requires one indirect result and no result values"
                                .into(),
                        );
                    }
                    let Some(ty) = signature.params.get(index as usize) else {
                        return Err("hidden result parameter is out of range".into());
                    };
                    if *ty != crate::ty::Ty::Ptr {
                        return Err(
                            "hidden result parameter is not the prelowered Ptr carrier".into()
                        );
                    }
                    if binding.carrier_offset != 0
                        || binding.carrier_bytes != u64::from(self.target.pointer_bytes)
                    {
                        return Err("hidden result carrier is not one complete pointer".into());
                    }
                    claim(&mut parameters, index, binding, "hidden result parameter")?;
                }
                AbiBindingPlace::Parameter(_) => {
                    return Err("source result has an ordinary parameter binding".into());
                }
            }
        }
        if parameters.iter().chain(&results).any(Vec::is_empty) {
            return Err("signature ABI omits a lowered parameter or result".into());
        }
        validate_carrier_bounds(&parameters, &signature.params, self.target.pointer_bytes)?;
        validate_carrier_bounds(&results, &signature.returns, self.target.pointer_bytes)?;
        Ok(())
    }

    pub fn validate_target(&self, target: Option<&crate::TargetInfo>) -> Result<(), String> {
        let Some(target) = target else {
            return Err("typed signature ABI requires module target information".into());
        };
        if self.target.triple != target.triple
            || u32::from(self.target.pointer_bytes) != target.pointer_size
            || self.target.little_endian != (target.endianness == crate::Endianness::Little)
            || target
                .abi
                .as_ref()
                .is_some_and(|abi| *abi != self.target.abi)
        {
            return Err("typed signature ABI target disagrees with the module target".into());
        }
        Ok(())
    }

    /// Legacy function facts may add no contradictory ABI claim. Missing
    /// legacy facts stay missing; they never overwrite the typed descriptor.
    pub fn reconcile_function(&self, function: &crate::Function) -> Result<(), String> {
        if function.calling_conv != self.lowered_convention {
            return Err("function convention disagrees with typed signature ABI".into());
        }
        for (index, attrs) in function.attrs.params.iter().enumerate() {
            if attrs.is_empty() {
                continue;
            }
            let owners = self.arguments.iter().chain(std::iter::once(&self.result))
                .flat_map(|arg| arg.bindings.iter().map(move |binding| (arg, binding)))
                .filter(|(_, binding)| matches!(binding.place,
                    AbiBindingPlace::Parameter(i) | AbiBindingPlace::HiddenResult(i) if i as usize == index));
            let mut found = false;
            for (arg, binding) in owners {
                // A lowered carrier can pack several source arguments. The
                // canonical slot attribute applies to that whole carrier,
                // so every owner must agree with it.
                reconcile_attrs(attrs, arg, binding)?;
                found = true;
            }
            if !found {
                return Err(format!(
                    "function attribute {index} has no typed ABI binding"
                ));
            }
        }
        if !function.attrs.ret.is_empty() {
            let [binding] = self.result.bindings.as_slice() else {
                return Err("return attributes require exactly one typed result binding".into());
            };
            if !matches!(binding.place, AbiBindingPlace::Result(_)) {
                return Err("return attributes disagree with a hidden result".into());
            }
            reconcile_attrs(&function.attrs.ret, &self.result, binding)?;
        }
        Ok(())
    }
}

fn reconcile_attrs(
    legacy: &crate::ParamAttrs,
    arg: &AbiArgument,
    binding: &AbiBinding,
) -> Result<(), String> {
    let indirect = matches!(arg.mode, AbiPassMode::Indirect { .. });
    let hidden = matches!(binding.place, AbiBindingPlace::HiddenResult(_));
    if legacy.sret && !hidden || legacy.byval && (!indirect || hidden) {
        return Err("function byval/sret attribute disagrees with typed ABI role".into());
    }
    let attrs = match &arg.mode {
        AbiPassMode::Direct(s) => &s.attributes,
        AbiPassMode::Pair(a, _)
            if binding.source_offset == a.source_offset
                && binding.source_bytes == a.source_bytes =>
        {
            &a.attributes
        }
        AbiPassMode::Pair(_, b)
            if binding.source_offset == b.source_offset
                && binding.source_bytes == b.source_bytes =>
        {
            &b.attributes
        }
        AbiPassMode::Cast { attributes, .. } | AbiPassMode::Indirect { attributes, .. } => {
            attributes
        }
        _ => return Err("function attributes do not identify one typed ABI carrier".into()),
    };
    let extension = match legacy.ext {
        crate::ArgExt::None => None,
        crate::ArgExt::SignExt => Some(AbiExtension::Sign),
        crate::ArgExt::ZeroExt => Some(AbiExtension::Zero),
    };
    if extension.is_some_and(|ext| ext != attrs.extension)
        || legacy.nonnull && !attrs.nonnull
        || legacy.noalias && !attrs.no_alias
        || legacy.readonly && !attrs.readonly
        || legacy
            .align
            .is_some_and(|align| Some(align) != attrs.pointee_align)
        || legacy
            .dereferenceable
            .is_some_and(|bytes| bytes != attrs.pointee_size)
    {
        return Err("function attributes disagree with typed ABI carrier attributes".into());
    }
    if let Some(pass) = &legacy.pass {
        let compatible = match pass {
            crate::PassMode::Ignore => matches!(arg.mode, AbiPassMode::Ignore),
            crate::PassMode::Direct => {
                matches!(arg.mode, AbiPassMode::Direct(_) | AbiPassMode::Pair(..))
            }
            crate::PassMode::Pair => {
                matches!(arg.mode, AbiPassMode::Pair(..)) && arg.bindings.len() == 1
            }
            crate::PassMode::Indirect { on_stack } => {
                matches!(arg.mode, AbiPassMode::Indirect { on_stack: actual, .. } if actual == *on_stack)
            }
            // Coarse legacy cast facts cannot distinguish live bytes from
            // padding or carry prefix/rest grouping. Retain one authority.
            crate::PassMode::Cast { .. } => false,
        };
        if !compatible {
            return Err(
                "function pass mode disagrees with or cannot refine the typed ABI mode".into(),
            );
        }
    }
    Ok(())
}

fn claim(
    census: &mut [Vec<(u64, u64)>],
    index: u32,
    binding: &AbiBinding,
    kind: &str,
) -> Result<(), String> {
    let Some(ranges) = census.get_mut(index as usize) else {
        return Err(format!("{kind} binding {index} is out of range"));
    };
    let end = binding
        .carrier_offset
        .checked_add(binding.carrier_bytes)
        .ok_or("carrier binding extent overflows")?;
    if binding.carrier_bytes == 0 {
        return Err("carrier binding extent is empty".into());
    }
    if ranges
        .iter()
        .any(|&(start, stop)| binding.carrier_offset < stop && start < end)
    {
        return Err(format!("{kind} binding {index} overlaps or is duplicated"));
    }
    ranges.push((binding.carrier_offset, end));
    Ok(())
}

fn validate_carrier_bounds(
    census: &[Vec<(u64, u64)>],
    types: &[crate::Ty],
    pointer_bytes: u8,
) -> Result<(), String> {
    use crate::Ty;
    for (ranges, ty) in census.iter().zip(types) {
        let bytes = match ty {
            Ty::Ptr
            | Ty::Func(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Isize
            | Ty::Usize => Some(u64::from(pointer_bytes)),
            Ty::Bool => Some(1),
            _ => ty.bit_width().map(|bits| u64::from(bits).div_ceil(8)),
        };
        // Aggregate layout belongs to the module's layout authority. Padding
        // need not have a source owner; every live source lane is checked below.
        if let Some(bytes) = bytes {
            let mut ranges = ranges.clone();
            ranges.sort_unstable();
            let mut cursor = 0;
            for (start, end) in ranges {
                if start != cursor || end > bytes {
                    return Err("scalar carrier census has a gap or exceeds its width".into());
                }
                cursor = end;
            }
            if cursor != bytes {
                return Err("scalar carrier census omits bytes".into());
            }
        }
    }
    Ok(())
}

fn validate_argument(arg: &AbiArgument, is_result: bool) -> Result<(), String> {
    if !arg.align.is_power_of_two() {
        return Err("source alignment is not a nonzero power of two".into());
    }
    if matches!(arg.mode, AbiPassMode::Ignore) {
        return if arg.bindings.is_empty() {
            Ok(())
        } else {
            Err("Ignore requires no lowered bindings".into())
        };
    }
    if arg.bindings.is_empty() || arg.size == 0 {
        return Err("non-ignored source value has no storage or no binding".into());
    }
    let mut extents = Vec::new();
    for binding in &arg.bindings {
        let end = binding
            .source_offset
            .checked_add(binding.source_bytes)
            .ok_or("source binding extent overflows")?;
        if binding.source_bytes == 0 || end > arg.size {
            return Err("source binding extent is empty or exceeds storage".into());
        }
        if extents
            .iter()
            .any(|&(start, stop)| binding.source_offset < stop && start < end)
        {
            return Err("source binding extents overlap".into());
        }
        extents.push((binding.source_offset, end));
    }
    match &arg.mode {
        AbiPassMode::Ignore => unreachable!(),
        AbiPassMode::Direct(a) => validate_scalar(a, arg.size)?,
        AbiPassMode::Pair(a, b) => {
            validate_scalar(a, arg.size)?;
            validate_scalar(b, arg.size)?;
            if a.source_offset < b.source_offset + b.source_bytes
                && b.source_offset < a.source_offset + a.source_bytes
            {
                return Err("pair source lanes overlap".into());
            }
        }
        AbiPassMode::Cast {
            prefix,
            rest_offset,
            rest,
            attributes,
            ..
        } => {
            validate_attributes(attributes)?;
            let mut end = 0u64;
            for reg in prefix {
                validate_register(reg)?;
                end = end
                    .checked_add(reg.bytes)
                    .ok_or("cast prefix extent overflows")?;
            }
            validate_register(&rest.unit)?;
            let offset = rest_offset.unwrap_or(end);
            if offset < end {
                return Err("cast rest overlaps its prefix".into());
            }
            let end = offset
                .checked_add(rest.total)
                .ok_or("cast extent overflows")?;
            if end == 0 || offset > arg.size || end > arg.size {
                return Err("cast live extent exceeds source storage".into());
            }
            if rest.total % rest.unit.bytes != 0 && rest.unit.class != AbiRegisterClass::Integer {
                return Err("only a final integer cast carrier may be partially live".into());
            }
        }
        AbiPassMode::Indirect {
            attributes,
            metadata_attributes,
            on_stack,
            caller_copy,
        } => {
            validate_attributes(attributes)?;
            if let Some(attrs) = metadata_attributes {
                validate_attributes(attrs)?;
                // This record has no separate data/metadata carrier role or
                // dynamic source extent. Treating ordinary byte bindings as
                // that transport would admit a scalar as an indirect value.
                // Keep the producer record representable, but refuse semantic
                // admission until those missing premises have a faithful model.
                return Err("unsized indirect metadata transport requires explicit data/metadata bindings and a dynamic source extent".into());
            }
            if is_result && (*on_stack || *caller_copy) {
                return Err("indirect result cannot be an argument stack copy".into());
            }
            if metadata_attributes.is_none()
                && (arg.bindings.len() != 1
                    || arg.bindings[0].source_offset != 0
                    || arg.bindings[0].source_bytes != arg.size)
            {
                return Err("indirect binding must describe the complete source storage".into());
            }
        }
    }
    // Every live scalar/cast source byte must occur in a lowered binding.
    // Padding may occur in a binding, but cannot substitute for a missing lane.
    let covered = |start: u64, bytes: u64| {
        let mut ranges: Vec<_> = arg
            .bindings
            .iter()
            .filter_map(|binding| {
                let source_end = binding.source_offset.checked_add(binding.source_bytes)?;
                let carrier_end = binding.source_offset.checked_add(binding.carrier_bytes)?;
                Some((binding.source_offset, source_end.min(carrier_end)))
            })
            .collect();
        ranges.sort_unstable();
        let mut cursor = start;
        for (low, high) in ranges {
            if low <= cursor && cursor < high {
                cursor = high;
            }
        }
        start.checked_add(bytes).is_some_and(|end| cursor >= end)
    };
    match &arg.mode {
        AbiPassMode::Direct(a) if !covered(a.source_offset, a.source_bytes) => {
            return Err("binding census omits a direct source lane".into());
        }
        AbiPassMode::Pair(a, b)
            if !covered(a.source_offset, a.source_bytes)
                || !covered(b.source_offset, b.source_bytes) =>
        {
            return Err("binding census omits a pair source lane".into());
        }
        AbiPassMode::Cast {
            prefix,
            rest_offset,
            rest,
            ..
        } => {
            let prefix_bytes: u64 = prefix.iter().map(|r| r.bytes).sum();
            if (prefix_bytes != 0 && !covered(0, prefix_bytes))
                || (rest.total != 0 && !covered(rest_offset.unwrap_or(prefix_bytes), rest.total))
            {
                return Err("binding census omits a cast source lane".into());
            }
        }
        _ => {}
    }
    Ok(())
}

fn validate_register(reg: &AbiRegister) -> Result<(), String> {
    if reg.bytes == 0 || reg.bytes > 256 {
        return Err("ABI carrier has an invalid width".into());
    }
    Ok(())
}

fn validate_scalar(scalar: &AbiScalar, size: u64) -> Result<(), String> {
    validate_register(&scalar.register)?;
    validate_attributes(&scalar.attributes)?;
    if scalar.value_bits == 0
        || u64::from(scalar.value_bits) > scalar.source_bytes.saturating_mul(8)
    {
        return Err("scalar defined-bit width is empty or exceeds live storage".into());
    }
    if scalar.source_bytes == 0
        || scalar.source_bytes > scalar.register.bytes
        || scalar
            .source_offset
            .checked_add(scalar.source_bytes)
            .is_none_or(|end| end > size)
    {
        return Err(
            "scalar live extent is empty, wider than its carrier, or outside storage".into(),
        );
    }
    if scalar.attributes.extension != AbiExtension::None
        && scalar.register.class != AbiRegisterClass::Integer
    {
        return Err("integer extension is recorded on a non-integer carrier".into());
    }
    Ok(())
}

fn validate_attributes(attrs: &AbiAttributes) -> Result<(), String> {
    if attrs
        .pointee_align
        .is_some_and(|align| !align.is_power_of_two())
    {
        return Err("pointee alignment is not a nonzero power of two".into());
    }
    Ok(())
}
