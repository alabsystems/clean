// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::CoercionKind;
use crate::types::{Mutability, RustType};

pub(super) fn try_coerce_ref_to_dyn_trait(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    if let (
        RustType::Reference {
            mutability: from_mut,
            inner: from_inner,
            ..
        },
        RustType::Reference {
            mutability: to_mut,
            inner: to_inner,
            ..
        },
    ) = (from, to)
    {
        if ref_unsize_mutability_allows(*from_mut, *to_mut)
            && can_directly_unsize_to_dyn_trait(from_inner.as_ref(), to_inner.as_ref())
        {
            return Some(CoercionKind::UnsizeToDynTrait);
        }
    }

    None
}

pub(super) fn try_coerce_box_unsize(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    if let (RustType::Box { inner: from_inner }, RustType::Box { inner: to_inner }) = (from, to) {
        if can_directly_unsize_to_dyn_trait(from_inner.as_ref(), to_inner.as_ref()) {
            return Some(CoercionKind::UnsizeToDynTrait);
        }
    }

    None
}

pub(super) fn try_deref_unsize_to_dyn_trait(
    src: &RustType,
    dst: &RustType,
    from_ref_mutability: Mutability,
    target_ref_mutability: Mutability,
) -> Option<CoercionKind> {
    if can_directly_unsize_to_dyn_trait(src, dst)
        && ref_unsize_mutability_allows(from_ref_mutability, target_ref_mutability)
    {
        return Some(CoercionKind::UnsizeToDynTrait);
    }

    None
}

fn ref_unsize_mutability_allows(
    from_ref_mutability: Mutability,
    target_ref_mutability: Mutability,
) -> bool {
    target_ref_mutability == Mutability::Shared || from_ref_mutability == Mutability::Mutable
}

fn can_directly_unsize_to_dyn_trait(src: &RustType, dst: &RustType) -> bool {
    is_dyn_trait_target(dst)
        && !matches!(src, RustType::DynTrait { .. })
        && !requires_indirection_before_unsizing(src)
}

fn is_dyn_trait_target(ty: &RustType) -> bool {
    matches!(ty, RustType::DynTrait { .. })
}

fn requires_indirection_before_unsizing(ty: &RustType) -> bool {
    matches!(ty, RustType::Reference { .. } | RustType::RawPtr { .. })
        || matches!(ty, RustType::Box { .. })
        || is_rc_or_arc(ty)
}

fn is_rc_or_arc(ty: &RustType) -> bool {
    matches!(
        ty,
        RustType::Named {
            name,
            type_args,
            ..
        } if matches!(
            name.as_str(),
            "Rc" | "std::rc::Rc" | "alloc::rc::Rc" | "Arc" | "std::sync::Arc" | "alloc::sync::Arc"
        ) && type_args.len() == 1
    )
}
