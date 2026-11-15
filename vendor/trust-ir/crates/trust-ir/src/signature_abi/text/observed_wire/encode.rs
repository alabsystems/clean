// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

pub(super) fn signature<O: ExecutionObserver>(a: &SignatureAbi, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{target=")?;
    target(&a.target, out)?;
    out.append(",frontend={name=")?;
    out.quoted(&a.frontend.name)?;
    out.append(",revision=")?;
    out.quoted(&a.frontend.revision)?;
    out.append("},convention=")?;
    out.quoted(&a.convention)?;
    out.append(",lowered_convention=")?;
    out.quoted(convention(a.lowered_convention))?;
    out.append(",source_abi=")?;
    out.quoted(&a.source_abi)?;
    out.append(",can_unwind=")?;
    out.boolean(a.can_unwind)?;
    out.append(",variadic=")?;
    out.boolean(a.variadic)?;
    out.append(",fixed_count=")?;
    out.number(u64::from(a.fixed_count))?;
    out.append(",arguments=[")?;
    for (index, arg) in a.arguments.iter().enumerate() {
        out.poll()?;
        if index != 0 {
            out.append(",")?;
        }
        argument(arg, out)?;
    }
    out.append("],result=")?;
    argument(&a.result, out)?;
    out.append("}")
}
fn convention(value: crate::CallingConv) -> &'static str {
    match value {
        crate::CallingConv::C => "ccc",
        crate::CallingConv::Fast => "fastcc",
        crate::CallingConv::Cold => "coldcc",
        crate::CallingConv::Rust => "rustcc",
        crate::CallingConv::Swift => "swiftcc",
        crate::CallingConv::SysV64 => "sysv64cc",
        crate::CallingConv::Win64 => "win64cc",
        crate::CallingConv::Aapcs => "aapcscc",
        crate::CallingConv::EfiApi => "efiapicc",
        crate::CallingConv::VectorCall => "vectorcallcc",
        crate::CallingConv::CUnwind => "c_unwindcc",
        crate::CallingConv::RustCold => "rust_coldcc",
    }
}
fn target<O: ExecutionObserver>(a: &AbiTarget, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{triple=")?;
    out.quoted(&a.triple)?;
    out.append(",data_layout=")?;
    out.quoted(&a.data_layout)?;
    out.append(",abi=")?;
    out.quoted(&a.abi)?;
    out.append(",cpu=")?;
    out.quoted(&a.cpu)?;
    out.append(",features=[")?;
    for (index, feature) in a.features.iter().enumerate() {
        out.poll()?;
        if index != 0 {
            out.append(",")?;
        }
        out.quoted(feature)?;
    }
    out.append("],target_spec=")?;
    out.quoted(&a.target_spec)?;
    out.append(",pointer_bytes=")?;
    out.number(u64::from(a.pointer_bytes))?;
    out.append(",little_endian=")?;
    out.boolean(a.little_endian)?;
    out.append("}")
}
fn argument<O: ExecutionObserver>(a: &AbiArgument, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{size=")?;
    out.number(a.size)?;
    out.append(",align=")?;
    out.number(a.align)?;
    out.append(",mode=")?;
    mode(&a.mode, out)?;
    out.append(",bindings=[")?;
    for (index, binding) in a.bindings.iter().enumerate() {
        out.poll()?;
        if index != 0 {
            out.append(",")?;
        }
        write_binding(binding, out)?;
    }
    out.append("]}")
}
fn write_binding<O: ExecutionObserver>(a: &AbiBinding, out: &mut Writer<'_, '_, O>) -> R {
    let (place, index) = match a.place {
        AbiBindingPlace::Parameter(index) => ("parameter", index),
        AbiBindingPlace::Result(index) => ("result", index),
        AbiBindingPlace::HiddenResult(index) => ("hidden_result", index),
    };
    out.append("{place=")?;
    out.quoted(place)?;
    out.append(",index=")?;
    out.number(u64::from(index))?;
    out.append(",source_offset=")?;
    out.number(a.source_offset)?;
    out.append(",source_bytes=")?;
    out.number(a.source_bytes)?;
    out.append(",carrier_offset=")?;
    out.number(a.carrier_offset)?;
    out.append(",carrier_bytes=")?;
    out.number(a.carrier_bytes)?;
    out.append("}")
}
fn register<O: ExecutionObserver>(a: &AbiRegister, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{class=")?;
    out.quoted(match a.class {
        AbiRegisterClass::Integer => "integer",
        AbiRegisterClass::Float => "float",
        AbiRegisterClass::Vector => "vector",
    })?;
    out.append(",bytes=")?;
    out.number(a.bytes)?;
    out.append("}")
}
fn scalar<O: ExecutionObserver>(a: &AbiScalar, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{register=")?;
    register(&a.register, out)?;
    out.append(",source_offset=")?;
    out.number(a.source_offset)?;
    out.append(",source_bytes=")?;
    out.number(a.source_bytes)?;
    out.append(",value_bits=")?;
    out.number(u64::from(a.value_bits))?;
    out.append(",attributes=")?;
    attributes(&a.attributes, out)?;
    out.append("}")
}
fn uniform<O: ExecutionObserver>(a: &AbiUniform, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{unit=")?;
    register(&a.unit, out)?;
    out.append(",total=")?;
    out.number(a.total)?;
    out.append(",consecutive=")?;
    out.boolean(a.consecutive)?;
    out.append("}")
}
fn option_number<O: ExecutionObserver>(a: Option<u64>, out: &mut Writer<'_, '_, O>) -> R {
    match a {
        Some(value) => out.number(value),
        None => out.append("none"),
    }
}
fn attributes<O: ExecutionObserver>(a: &AbiAttributes, out: &mut Writer<'_, '_, O>) -> R {
    out.append("{extension=")?;
    out.quoted(match a.extension {
        AbiExtension::None => "none",
        AbiExtension::Sign => "sign",
        AbiExtension::Zero => "zero",
    })?;
    for (key, value) in [
        ("in_reg", a.in_reg),
        ("no_alias", a.no_alias),
        ("nonnull", a.nonnull),
        ("readonly", a.readonly),
        ("no_undef", a.no_undef),
        ("writable", a.writable),
        ("no_free", a.no_free),
    ] {
        out.poll()?;
        out.append(",")?;
        out.append(key)?;
        out.append("=")?;
        out.boolean(value)?;
    }
    out.append(",capture=")?;
    out.quoted(match a.capture {
        AbiCapture::Any => "any",
        AbiCapture::ReadOnly => "readonly",
        AbiCapture::Address => "address",
        AbiCapture::None => "none",
    })?;
    out.append(",pointee_size=")?;
    out.number(a.pointee_size)?;
    out.append(",pointee_align=")?;
    option_number(a.pointee_align, out)?;
    out.append("}")
}
fn mode<O: ExecutionObserver>(a: &AbiPassMode, out: &mut Writer<'_, '_, O>) -> R {
    match a {
        AbiPassMode::Ignore => out.append("{kind=\"ignore\"}"),
        AbiPassMode::Direct(value) => {
            out.append("{kind=\"direct\",scalar=")?;
            scalar(value, out)?;
            out.append("}")
        }
        AbiPassMode::Pair(first, second) => {
            out.append("{kind=\"pair\",first=")?;
            scalar(first, out)?;
            out.append(",second=")?;
            scalar(second, out)?;
            out.append("}")
        }
        AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes: attrs,
        } => {
            out.append("{kind=\"cast\",pad_i32=")?;
            out.boolean(*pad_i32)?;
            out.append(",prefix=[")?;
            for (index, value) in prefix.iter().enumerate() {
                out.poll()?;
                if index != 0 {
                    out.append(",")?;
                }
                register(value, out)?;
            }
            out.append("],rest_offset=")?;
            option_number(*rest_offset, out)?;
            out.append(",rest=")?;
            uniform(rest, out)?;
            out.append(",attributes=")?;
            attributes(attrs, out)?;
            out.append("}")
        }
        AbiPassMode::Indirect {
            attributes: attrs,
            metadata_attributes,
            on_stack,
            caller_copy,
        } => {
            out.append("{kind=\"indirect\",attributes=")?;
            attributes(attrs, out)?;
            out.append(",metadata_attributes=")?;
            match metadata_attributes {
                Some(value) => attributes(value, out)?,
                None => out.append("none")?,
            }
            out.append(",on_stack=")?;
            out.boolean(*on_stack)?;
            out.append(",caller_copy=")?;
            out.boolean(*caller_copy)?;
            out.append("}")
        }
    }
}
