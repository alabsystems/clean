// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
mod enums;
mod lookup;
pub(super) fn enum_tail<O: ExecutionObserver>(
    s: &mut State<'_>,
    a: &EnumDef,
    b: &EnumDef,
    w: &mut Work<'_, '_, O>,
) -> R {
    enums::tail(s, a, b, w)
}
pub(super) fn pair<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    kind: Kind,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(
        1 + 2 * size_of::<crate::ty::StructDef>()
            + 2 * size_of::<EnumDef>()
            + 2 * size_of::<crate::ty::RecordDef>()
            + 2 * size_of::<crate::ty::ClosureTy>()
            + 2 * size_of::<crate::FuncTy>(),
        4 * size_of::<usize>(),
    )?;
    match kind {
        Kind::Struct => strukt(s, a, b, left, right, w),
        Kind::Enum => enm(s, a, b, left, right, w),
        Kind::Record => record(s, a, b, left, right, w),
        Kind::Closure => closure(s, a, b, left, right, w),
        Kind::Func => func(s, a, b, left, right, w),
        Kind::TyId | Kind::Pred => Err(ObservedValueError::InvalidRange),
    }
}
fn strukt<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    let (Some(da), Some(db)) = (
        lookup::strukt(&a.structs, left, w)?,
        lookup::strukt(&b.structs, right, w)?,
    ) else {
        s.last = false;
        return Ok(());
    };
    let shared = shared(&da.origin, &db.origin, w)?;
    if matches!(shared, Origin::Different) {
        s.last = false;
        return Ok(());
    }
    let source = conflict(shared, "struct", &da.name, &db.name);
    if s.enter((Kind::Struct, left, right), source, w)? {
        s.last = w.text(da.name.as_bytes(), db.name.as_bytes())?
            && da.repr == db.repr
            && da.size == db.size
            && da.align == db.align
            && da.fields.len() == db.fields.len();
        if s.last {
            s.push(Task::Fields(&da.fields, &db.fields), w)?;
        }
    }

    Ok(())
}
fn enm<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    let (Some(da), Some(db)) = (
        lookup::enm(&a.enums, left, w)?,
        lookup::enm(&b.enums, right, w)?,
    ) else {
        s.last = false;
        return Ok(());
    };
    let shared = shared(&da.origin, &db.origin, w)?;
    if matches!(shared, Origin::Different) {
        s.last = false;
        return Ok(());
    }
    let source = conflict(shared, "enum", &da.name, &db.name);
    if s.enter((Kind::Enum, left, right), source, w)? {
        s.last = w.text(da.name.as_bytes(), db.name.as_bytes())?
            && da.variants.len() == db.variants.len();
        if s.last {
            s.push(Task::EnumTail(da, db), w)?;
            s.push(Task::Variants(&da.variants, &db.variants), w)?;
        }
    }

    Ok(())
}
fn record<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    let (Some(da), Some(db)) = (
        lookup::record(&a.records, left, w)?,
        lookup::record(&b.records, right, w)?,
    ) else {
        s.last = false;
        return Ok(());
    };
    if s.enter((Kind::Record, left, right), None, w)? {
        s.last =
            w.text(da.name.as_bytes(), db.name.as_bytes())? && da.fields.len() == db.fields.len();
        if s.last {
            s.push(Task::Fields(&da.fields, &db.fields), w)?;
        }
    }

    Ok(())
}
fn closure<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    let (Some(da), Some(db)) = (
        a.closure_types.get(left as usize),
        b.closure_types.get(right as usize),
    ) else {
        s.last = false;
        return Ok(());
    };
    if s.enter((Kind::Closure, left, right), None, w)? {
        s.push(Task::Types(&da.captures, &db.captures), w)?;
        s.push(
            Task::Nominal(Kind::Func, da.func.index(), db.func.index()),
            w,
        )?;
    }

    Ok(())
}
fn func<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    left: u32,
    right: u32,
    w: &mut Work<'_, '_, O>,
) -> R {
    let (Some(da), Some(db)) = (
        a.func_types.get(left as usize),
        b.func_types.get(right as usize),
    ) else {
        s.last = false;
        return Ok(());
    };
    if s.enter((Kind::Func, left, right), None, w)? {
        s.last = da.is_vararg == db.is_vararg
            && crate::func_ty_equality_observed::signature_abi_eq_observed(
                da.abi.as_ref(),
                db.abi.as_ref(),
                w.session,
                w.site,
            )?
            && da.params.len() == db.params.len()
            && da.returns.len() == db.returns.len();
        if s.last {
            s.push(Task::Types(&da.returns, &db.returns), w)?;
            s.push(Task::Types(&da.params, &db.params), w)?;
        }
    }

    Ok(())
}

enum Origin<'a> {
    Shared(&'a TypeOrigin),
    Unkeyed,
    Different,
}
fn shared<'a, O: ExecutionObserver>(
    a: &'a Option<TypeOrigin>,
    b: &'a Option<TypeOrigin>,
    w: &mut Work<'_, '_, O>,
) -> R<Origin<'a>> {
    w.admit(
        1 + 2 * size_of::<TypeOrigin>(),
        2 * size_of::<Option<&TypeOrigin>>(),
    )?;
    match (a, b) {
        (Some(a), Some(b)) => {
            let equal = match (a, b) {
                (
                    TypeOrigin::Rust {
                        stable_crate_id: a,
                        def_path_hash: da,
                        args_digest: ga,
                    },
                    TypeOrigin::Rust {
                        stable_crate_id: b,
                        def_path_hash: db,
                        args_digest: gb,
                    },
                ) => a == b && da == db && ga == gb,
                (
                    TypeOrigin::Clean {
                        decl: a,
                        env_digest: da,
                    },
                    TypeOrigin::Clean {
                        decl: b,
                        env_digest: db,
                    },
                ) => w.text(a.as_bytes(), b.as_bytes())? && da == db,
                _ => false,
            };
            Ok(if equal {
                Origin::Shared(a)
            } else {
                Origin::Different
            })
        }
        _ => Ok(Origin::Unkeyed),
    }
}
fn conflict<'a>(
    shared: Origin<'a>,
    table: &'static str,
    left: &'a str,
    right: &'a str,
) -> Option<ConflictSource<'a>> {
    match shared {
        Origin::Shared(origin) => Some(ConflictSource {
            origin,
            table,
            left,
            right,
        }),
        _ => None,
    }
}
pub(super) fn fields<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [FieldDef],
    b: &'a [FieldDef],
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(
        1 + 2 * size_of::<FieldDef>(),
        2 * size_of::<Option<(&FieldDef, &[FieldDef])>>(),
    )?;
    if a.len() != b.len() {
        s.last = false;
        return Ok(());
    }
    if let (Some((a, rest_a)), Some((b, rest_b))) = (a.split_first(), b.split_first()) {
        s.last = w.text(a.name.as_bytes(), b.name.as_bytes())? && a.offset == b.offset;
        if s.last {
            s.push(Task::Fields(rest_a, rest_b), w)?;
            s.push(Task::Ty(&a.ty, &b.ty), w)?;
        }
    }
    Ok(())
}
pub(super) fn variants<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [EnumVariant],
    b: &'a [EnumVariant],
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1, 2 * size_of::<Option<(&EnumVariant, &[EnumVariant])>>())?;
    if a.len() != b.len() {
        s.last = false;
        return Ok(());
    }
    if let (Some((a, rest_a)), Some((b, rest_b))) = (a.split_first(), b.split_first()) {
        s.last = w.text(a.name.as_bytes(), b.name.as_bytes())? && a.fields.len() == b.fields.len();
        if s.last {
            s.push(Task::Variants(rest_a, rest_b), w)?;
            s.push(Task::Types(&a.fields, &b.fields), w)?;
        }
    }
    Ok(())
}
