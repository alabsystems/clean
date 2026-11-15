// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn function<O: ExecutionObserver>(
        &mut self,
        v: &'a FuncTy,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<FuncTy>())?;
        let FuncTy {
            params,
            returns,
            is_vararg,
            abi,
        } = v;
        self.push(Task::Text(" }"), work)?;
        match abi {
            None => self.push(Task::Text("None"), work)?,
            Some(a) => {
                scheduled!(self, work; [Task::Text("Some("), Task::Signature(a), Task::Text(")")])?
            }
        };
        scheduled!(self, work; [
            Task::Text("FuncTyG { params: ["),
            Task::List(List::Types(params), true),
            Task::Text("], returns: ["),
            Task::List(List::Types(returns), true),
            Task::Text("], is_vararg: "),
            Task::Bool(*is_vararg),
            Task::Text(", abi: "),
        ])
    }
    pub(super) fn signature<O: ExecutionObserver>(
        &mut self,
        v: &'a SignatureAbi,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<SignatureAbi>())?;
        let SignatureAbi {
            target,
            frontend,
            convention,
            lowered_convention,
            source_abi,
            can_unwind,
            variadic,
            fixed_count,
            arguments,
            result,
        } = v;
        let AbiTarget {
            triple,
            data_layout,
            abi,
            cpu,
            features,
            target_spec,
            pointer_bytes,
            little_endian,
        } = target;
        let AbiFrontend { name, revision } = frontend;
        scheduled!(self, work; [
            Task::Text("SignatureAbi { target: AbiTarget { triple: "),
            Task::Quoted(triple),
            Task::Text(", data_layout: "),
            Task::Quoted(data_layout),
            Task::Text(", abi: "),
            Task::Quoted(abi),
            Task::Text(", cpu: "),
            Task::Quoted(cpu),
            Task::Text(", features: ["),
            Task::List(List::Strings(features), true),
            Task::Text("], target_spec: "),
            Task::Quoted(target_spec),
            Task::Text(", pointer_bytes: "),
            Task::Num(u128::from(*pointer_bytes)),
            Task::Text(", little_endian: "),
            Task::Bool(*little_endian),
            Task::Text(" }, frontend: AbiFrontend { name: "),
            Task::Quoted(name),
            Task::Text(", revision: "),
            Task::Quoted(revision),
            Task::Text(" }, convention: "),
            Task::Quoted(convention),
            Task::Text(", lowered_convention: "),
            Task::Text(match lowered_convention {
                crate::CallingConv::C => "C",
                crate::CallingConv::Fast => "Fast",
                crate::CallingConv::Cold => "Cold",
                crate::CallingConv::Rust => "Rust",
                crate::CallingConv::Swift => "Swift",
                crate::CallingConv::CUnwind => "CUnwind",
                crate::CallingConv::SysV64 => "SysV64",
                crate::CallingConv::Win64 => "Win64",
                crate::CallingConv::Aapcs => "Aapcs",
                crate::CallingConv::EfiApi => "EfiApi",
                crate::CallingConv::VectorCall => "VectorCall",
                crate::CallingConv::RustCold => "RustCold",
            }),
            Task::Text(", source_abi: "),
            Task::Quoted(source_abi),
            Task::Text(", can_unwind: "),
            Task::Bool(*can_unwind),
            Task::Text(", variadic: "),
            Task::Bool(*variadic),
            Task::Text(", fixed_count: "),
            Task::Num(u128::from(*fixed_count)),
            Task::Text(", arguments: ["),
            Task::List(List::Arguments(arguments), true),
            Task::Text("], result: "),
            Task::Argument(result),
            Task::Text(" }"),
        ])
    }
    pub(super) fn argument<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiArgument,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiArgument>())?;
        let AbiArgument {
            size,
            align,
            mode,
            bindings,
        } = v;
        scheduled!(self, work; [
            Task::Text("AbiArgument { size: "),
            Task::Num(u128::from(*size)),
            Task::Text(", align: "),
            Task::Num(u128::from(*align)),
            Task::Text(", mode: "),
            Task::Pass(mode),
            Task::Text(", bindings: "),
            Task::Text("["),
            Task::List(List::Bindings(bindings), true),
            Task::Text("]"),
            Task::Text(" }"),
        ])
    }
    pub(super) fn scalar<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiScalar,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiScalar>())?;
        let AbiScalar {
            register,
            source_offset,
            source_bytes,
            value_bits,
            attributes,
        } = v;
        scheduled!(self, work; [
            Task::Text("AbiScalar { register: "),
            Task::Register(register),
            Task::Text(", source_offset: "),
            Task::Num(u128::from(*source_offset)),
            Task::Text(", source_bytes: "),
            Task::Num(u128::from(*source_bytes)),
            Task::Text(", value_bits: "),
            Task::Num(u128::from(*value_bits)),
            Task::Text(", attributes: "),
            Task::Attributes(attributes),
            Task::Text(" }"),
        ])
    }
    pub(super) fn uniform<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiUniform,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiUniform>())?;
        let AbiUniform {
            unit,
            total,
            consecutive,
        } = v;
        scheduled!(self, work; [
            Task::Text("AbiUniform { unit: "),
            Task::Register(unit),
            Task::Text(", total: "),
            Task::Num(u128::from(*total)),
            Task::Text(", consecutive: "),
            Task::Bool(*consecutive),
            Task::Text(" }"),
        ])
    }
    pub(super) fn register<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiRegister,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiRegister>())?;
        let AbiRegister { class, bytes } = v;
        scheduled!(self, work; [
            Task::Text("AbiRegister { class: "),
            Task::Text(match class {
                AbiRegisterClass::Integer => "Integer",
                AbiRegisterClass::Float => "Float",
                AbiRegisterClass::Vector => "Vector",
            }),
            Task::Text(", bytes: "),
            Task::Num(u128::from(*bytes)),
            Task::Text(" }"),
        ])
    }
    pub(super) fn binding<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiBinding,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiBinding>())?;
        let AbiBinding {
            place,
            source_offset,
            source_bytes,
            carrier_offset,
            carrier_bytes,
        } = v;
        let (name, n) = match place {
            AbiBindingPlace::Parameter(n) => ("Parameter(", n),
            AbiBindingPlace::Result(n) => ("Result(", n),
            AbiBindingPlace::HiddenResult(n) => ("HiddenResult(", n),
        };
        scheduled!(self, work; [
            Task::Text("AbiBinding { place: "),
            Task::Text(name),
            Task::Num(u128::from(*n)),
            Task::Text("), source_offset: "),
            Task::Num(u128::from(*source_offset)),
            Task::Text(", source_bytes: "),
            Task::Num(u128::from(*source_bytes)),
            Task::Text(", carrier_offset: "),
            Task::Num(u128::from(*carrier_offset)),
            Task::Text(", carrier_bytes: "),
            Task::Num(u128::from(*carrier_bytes)),
            Task::Text(" }"),
        ])
    }
    pub(super) fn attributes<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiAttributes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiAttributes>())?;
        let AbiAttributes {
            extension,
            in_reg,
            no_alias,
            nonnull,
            readonly,
            no_undef,
            writable,
            no_free,
            capture,
            pointee_size,
            pointee_align,
        } = v;
        scheduled!(self, work; [
            Task::Text("AbiAttributes { extension: "),
            Task::Text(match extension {
                AbiExtension::None => "None",
                AbiExtension::Sign => "Sign",
                AbiExtension::Zero => "Zero",
            }),
            Task::Text(", in_reg: "),
            Task::Bool(*in_reg),
            Task::Text(", no_alias: "),
            Task::Bool(*no_alias),
            Task::Text(", nonnull: "),
            Task::Bool(*nonnull),
            Task::Text(", readonly: "),
            Task::Bool(*readonly),
            Task::Text(", no_undef: "),
            Task::Bool(*no_undef),
            Task::Text(", writable: "),
            Task::Bool(*writable),
            Task::Text(", no_free: "),
            Task::Bool(*no_free),
            Task::Text(", capture: "),
            Task::Text(match capture {
                AbiCapture::Any => "Any",
                AbiCapture::ReadOnly => "ReadOnly",
                AbiCapture::Address => "Address",
                AbiCapture::None => "None",
            }),
            Task::Text(", pointee_size: "),
            Task::Num(u128::from(*pointee_size)),
            Task::Text(", pointee_align: "),
            Task::OptNum(*pointee_align),
            Task::Text(" }"),
        ])
    }
    pub(super) fn pass<O: ExecutionObserver>(
        &mut self,
        v: &'a AbiPassMode,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<AbiPassMode>())?;
        match v {
            AbiPassMode::Ignore => work.text("Ignore", &mut self.output),
            AbiPassMode::Direct(s) => {
                scheduled!(self, work; [Task::Text("Direct("), Task::Scalar(s), Task::Text(")")])
            }
            AbiPassMode::Pair(a, b) => scheduled!(self, work; [
                Task::Text("Pair("),
                Task::Scalar(a),
                Task::Text(", "),
                Task::Scalar(b),
                Task::Text(")"),
            ]),
            AbiPassMode::Cast {
                pad_i32,
                prefix,
                rest_offset,
                rest,
                attributes,
            } => scheduled!(self, work; [
                Task::Text("Cast { pad_i32: "),
                Task::Bool(*pad_i32),
                Task::Text(", prefix: ["),
                Task::List(List::Registers(prefix), true),
                Task::Text("], rest_offset: "),
                Task::OptNum(*rest_offset),
                Task::Text(", rest: "),
                Task::Uniform(rest),
                Task::Text(", attributes: "),
                Task::Attributes(attributes),
                Task::Text(" }"),
            ]),
            AbiPassMode::Indirect {
                attributes,
                metadata_attributes,
                on_stack,
                caller_copy,
            } => {
                scheduled!(self, work; [
                    Task::Text(", on_stack: "),
                    Task::Bool(*on_stack),
                    Task::Text(", caller_copy: "),
                    Task::Bool(*caller_copy),
                    Task::Text(" }"),
                ])?;
                match metadata_attributes {
                    None => self.push(Task::Text("None"), work)?,
                    Some(a) => {
                        scheduled!(self, work; [Task::Text("Some("), Task::Attributes(a), Task::Text(")")])?
                    }
                };
                scheduled!(self, work; [
                    Task::Text("Indirect { attributes: "),
                    Task::Attributes(attributes),
                    Task::Text(", metadata_attributes: "),
                ])
            }
        }
    }
}
