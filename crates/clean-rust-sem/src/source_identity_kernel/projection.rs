//! Strict projection of ORIGINAL source syntax, before the general source
//! reader can erase an unsupported macro/item. This is a closed mathematical
//! fragment reader, not a Rust type checker or a new compiler lowering.
use super::{SourceBody, SourceIdentityError};

/// Original text and exact lexical binder for this source-model claim. These
/// are not Rustc StableDef/Instance identities and authorize no missing TCX.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentitySource {
    source: String,
    function: String,
    parameter: String,
    body: SourceBody,
}
impl IdentitySource {
    pub fn original_text(&self) -> &str {
        &self.source
    }
    pub fn function(&self) -> &str {
        &self.function
    }
    pub fn parameter(&self) -> &str {
        &self.parameter
    }
    pub fn body(&self) -> &SourceBody {
        &self.body
    }
    pub fn claim(&self) -> Result<clean_kernel::Expr, SourceIdentityError> {
        Ok(super::declarations::identity_claim(self.body.reflect()?))
    }
    /// Untrusted candidate; replay reprojects its own original source text and
    /// checks against the reconstructed claim in a new canonical environment.
    pub fn proof_candidate(&self) -> Result<clean_kernel::Expr, SourceIdentityError> {
        Ok(super::declarations::identity_proof(self.body.reflect()?))
    }
}

/// Project exactly one safe, non-generic u64->u64 function from original text.
/// Every original statement is examined. No dropped macro, local/item, trailing
/// statement, call, cast, projection, attribute or implicit parameter is allowed.
pub fn project_identity_source(source: &str) -> Result<IdentitySource, SourceIdentityError> {
    let file =
        syn::parse_file(source).map_err(|_| SourceIdentityError::Unsupported("source syntax"))?;
    let [syn::Item::Fn(function)] = file.items.as_slice() else {
        return Err(SourceIdentityError::Unsupported(
            "requires exactly one original source function",
        ));
    };
    let sig = &function.sig;
    let uint = |ty: &syn::Type| {
        matches!(ty,syn::Type::Path(path) if path.qself.is_none()
        && path.path.is_ident("u64"))
    };
    if !file.attrs.is_empty()
        || file.shebang.is_some()
        || !function.attrs.is_empty()
        || sig.constness.is_some()
        || sig.asyncness.is_some()
        || sig.unsafety.is_some()
        || sig.abi.is_some()
        || !sig.generics.params.is_empty()
        || sig.generics.where_clause.is_some()
        || sig.variadic.is_some()
        || sig.inputs.len() != 1
    {
        return Err(SourceIdentityError::Unsupported(
            "requires a closed safe u64 -> u64 source signature",
        ));
    }
    let Some(syn::FnArg::Typed(parameter)) = sig.inputs.first() else {
        return Err(SourceIdentityError::Unsupported("source parameter"));
    };
    let syn::Pat::Ident(binding) = parameter.pat.as_ref() else {
        return Err(SourceIdentityError::Unsupported("source binding pattern"));
    };
    if !parameter.attrs.is_empty()
        || !binding.attrs.is_empty()
        || binding.by_ref.is_some()
        || binding.mutability.is_some()
        || binding.subpat.is_some()
        || !uint(&parameter.ty)
        || !matches!(&sig.output,syn::ReturnType::Type(_,ty) if uint(ty))
    {
        return Err(SourceIdentityError::Unsupported(
            "requires an exact immutable u64 argument and result",
        ));
    }
    let parameter = binding.ident.to_string();
    fn block(
        block: &syn::Block,
        name: &str,
        depth: usize,
    ) -> Result<SourceBody, SourceIdentityError> {
        let [syn::Stmt::Expr(expr, semi)] = block.stmts.as_slice() else {
            return Err(SourceIdentityError::Unsupported(
                "source block requires its one complete tail/return statement",
            ));
        };
        if semi.is_some() && !matches!(expr, syn::Expr::Return(_)) {
            return Err(SourceIdentityError::Unsupported(
                "discarded source value is not a return",
            ));
        }
        Ok(SourceBody::Block(Box::new(project(expr, name, depth + 1)?)))
    }
    fn project(
        expr: &syn::Expr,
        name: &str,
        depth: usize,
    ) -> Result<SourceBody, SourceIdentityError> {
        if depth >= 128 {
            return Err(SourceIdentityError::Unsupported("source projection depth"));
        }
        Ok(match expr {
            syn::Expr::Path(path)
                if path.attrs.is_empty() && path.qself.is_none() && path.path.is_ident(name) =>
            {
                SourceBody::Variable(0)
            }
            syn::Expr::Paren(expr) if expr.attrs.is_empty() => {
                SourceBody::Wrapper(Box::new(project(&expr.expr, name, depth + 1)?))
            }
            syn::Expr::Group(expr) if expr.attrs.is_empty() => {
                SourceBody::Wrapper(Box::new(project(&expr.expr, name, depth + 1)?))
            }
            syn::Expr::Block(expr) if expr.attrs.is_empty() && expr.label.is_none() => {
                block(&expr.block, name, depth)?
            }
            syn::Expr::Return(expr) if expr.attrs.is_empty() => {
                SourceBody::Return(Box::new(project(
                    expr.expr
                        .as_deref()
                        .ok_or(SourceIdentityError::Unsupported("missing return value"))?,
                    name,
                    depth + 1,
                )?))
            }
            _ => {
                return Err(SourceIdentityError::Unsupported(
                    "original source expression outside identity grammar",
                ))
            }
        })
    }
    Ok(IdentitySource {
        source: source.to_owned(),
        function: sig.ident.to_string(),
        body: block(&function.block, &parameter, 0)?,
        parameter,
    })
}
