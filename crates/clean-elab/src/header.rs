//! Header-only elaboration — a declaration's SIGNATURE, without its body.
//!
//! Clean's ordinary entry points ([`crate::elaborate_decl`] and the
//! `elaborate_decl_and_register*` family) elaborate a declaration's type AND
//! its body together. That makes name resolution depend on source order: a
//! declaration can only mention what an earlier declaration already registered.
//!
//! Header-first checking removes that dependence. Every declaration's header is
//! elaborated first, into a staging environment; only then is any body
//! elaborated. Resolution then sees the complete symbol table regardless of the
//! order declarations were written in — which is what lets one Clean island
//! name a declaration that a later island introduces.
//!
//! # A header is a type, not a proof
//!
//! A header is exactly what an `axiom` is: a name and a type, with no value. So
//! a staged header is, to everything downstream, indistinguishable from an
//! assumption the user never wrote. Installing headers where they can back a
//! kernel-certified proof would let `theorem a : False := b` and
//! `theorem b : False := a` certify each other.
//!
//! This module therefore produces headers and nothing else — it never
//! registers, and it takes `&Environment`, not `&mut`. The obligations named in
//! [`crate::ElabCtx::elab_decl_header_inner`] belong to the caller:
//!
//!   1. elaborate a body only once every declaration it depends on is a real,
//!      kernel-checked definition; and
//!   2. after registration, verify the registered term mentions no still-staged
//!      header.
//!
//! Obligation (2) is what makes the scheme robust rather than merely careful:
//! it is an exact, syntactic check on the elaborated term, so a dependency scan
//! that misses an edge can only cause a spurious rejection, never a proof
//! resting on a staged assumption.
//!
//! # `autoImplicit` interacts with header elaboration
//!
//! With `autoImplicit` on (the default), an unresolved name in a *type*
//! position is silently absorbed as a fresh implicit binder rather than
//! reported. A header elaborated under that setting can therefore invent a
//! binder where the author meant to name a declaration introduced elsewhere,
//! and the resulting header is wrong rather than absent. Under
//! `set_option autoImplicit false` the same signature fails to elaborate, this
//! module yields no header for it, and the declaration simply keeps
//! source-order semantics — which is the fail-closed direction.

use clean_kernel::{Environment, Expr, Name};
use clean_parser::{SurfaceBinder, SurfaceDecl, SurfaceExpr};

use crate::{ElabCtx, FileContext};

/// A declaration's signature, elaborated without its body.
#[derive(Debug, Clone)]
pub struct DeclHeader {
    /// Namespace-qualified name, exactly as the authoritative pass will
    /// register it — so a caller can match a header against a real declaration
    /// by name without re-deriving the qualification rules.
    pub name: Name,
    /// The universe parameters that actually survive in `ty`.
    pub universe_params: Vec<Name>,
    /// The elaborated type.
    pub ty: Expr,
}

/// Elaborate the headers a single top-level declaration introduces, without
/// elaborating any body and without registering anything.
///
/// Returns one entry per name the declaration would introduce that has an
/// elaborable signature. Nested forms (`namespace`, `section`, `mutual`,
/// `set_option ... in`) are walked, and names are qualified exactly as the
/// authoritative pass qualifies them.
///
/// This is **best effort by design**: a declaration whose signature does not
/// elaborate on its own — because it mentions a name no header has introduced
/// yet, or because its type must be inferred from its body (`def f := ...`
/// with no `: T`) — contributes no header. Such a declaration is not broken;
/// it simply cannot be forward-referenced, and keeps source-order semantics.
/// Errors are deliberately not surfaced: the authoritative pass elaborates the
/// same declaration again and is the one that must report.
///
/// `file_ctx` is read, never mutated — the caller's namespace/`open`/option
/// state is unaffected.
#[must_use]
pub fn elaborate_decl_headers_with_context(
    env: &Environment,
    decl: &SurfaceDecl,
    file_ctx: &FileContext,
) -> Vec<DeclHeader> {
    let mut fc = file_ctx.clone();
    let mut headers = Vec::new();
    collect_headers(env, decl, &mut fc, &mut headers);
    headers
}

fn collect_headers(
    env: &Environment,
    decl: &SurfaceDecl,
    fc: &mut FileContext,
    out: &mut Vec<DeclHeader>,
) {
    match decl {
        // Nested forms: walk them so a declaration inside a `namespace` block
        // is staged under the name it will really be registered as. The
        // enter/push/pop/exit sequence mirrors the namespace arm of
        // `elaborate_decl_and_register_inner_with_aux` so qualification and
        // alias scoping agree with the authoritative pass.
        SurfaceDecl::Namespace { name, decls, .. } => {
            fc.namespace_state_mut()
                .enter_namespace(Name::from_string(name));
            fc.namespace_state_mut().push_scope();
            fc.enter_local_scope();
            for inner in decls {
                collect_headers(env, inner, fc, out);
            }
            fc.exit_local_scope();
            fc.namespace_state_mut().pop_scope();
            fc.namespace_state_mut().exit_namespace();
        }
        SurfaceDecl::Section { decls, .. } => {
            fc.namespace_state_mut().push_scope();
            fc.enter_local_scope();
            for inner in decls {
                collect_headers(env, inner, fc, out);
            }
            fc.exit_local_scope();
            fc.namespace_state_mut().pop_scope();
        }
        // A `mutual` block already resolves its members against each other, so
        // its own bodies need nothing from us — but the block as a whole can
        // still be forward-referenced from another island, which is exactly
        // what staging its members' headers buys.
        SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                collect_headers(env, inner, fc, out);
            }
        }
        SurfaceDecl::SetOption {
            body: Some(inner), ..
        } => collect_headers(env, inner, fc, out),

        // Leaves that introduce exactly one name with a written signature.
        //
        // `Def` is included only when its type is written. `def f := <body>`
        // has no signature to elaborate — its type comes from its body, which
        // is precisely what header-first must not look at — so it contributes
        // no header.
        SurfaceDecl::Def {
            name,
            universe_params,
            binders,
            ty: Some(ty),
            ..
        } => push_header(env, fc, name, universe_params, binders, ty, out),
        SurfaceDecl::Theorem {
            name,
            universe_params,
            binders,
            ty,
            ..
        }
        | SurfaceDecl::Axiom {
            name,
            universe_params,
            binders,
            ty,
            ..
        }
        | SurfaceDecl::Opaque {
            name,
            universe_params,
            binders,
            ty,
            ..
        } => push_header(env, fc, name, universe_params, binders, ty, out),

        // Everything else introduces no forward-referenceable header here.
        //
        // `inductive` and `structure` are the notable omissions: each
        // introduces a family of names (the type, its constructors, its
        // recursors, projections) whose staging is a strictly larger job than
        // elaborating one signature, and a PARTIAL family would be worse than
        // none — a body could resolve the type name while failing to see its
        // constructors. They keep source-order semantics until staged as a unit.
        _ => {}
    }
}

fn push_header(
    env: &Environment,
    fc: &FileContext,
    name: &str,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    out: &mut Vec<DeclHeader>,
) {
    let mut ctx = ElabCtx::new(env);
    ctx.set_namespace_state(fc.namespace_state().clone());
    ctx.set_instance_scope_state(
        fc.dead_local_instances().clone(),
        fc.scoped_instance_map().clone(),
        fc.default_instance_entries(),
    );
    if let Ok((name, universe_params, ty)) =
        ctx.elab_decl_header_inner(name, universe_params, binders, ty)
    {
        out.push(DeclHeader {
            name,
            universe_params,
            ty,
        });
    }
}
