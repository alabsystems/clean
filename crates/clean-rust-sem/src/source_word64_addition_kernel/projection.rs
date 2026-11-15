//! Strict independent ORIGINAL syntax projection, not IR or a general Rust reader.
use super::{declarations, Expr, SourceBody, Word64AdditionError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdditionSource {
    source: String,
    function: String,
    parameter: String,
    body: SourceBody,
}
impl AdditionSource {
    pub fn original_text(&self) -> &str {
        &self.source
    }
    pub fn function(&self) -> &str {
        &self.function
    }
    pub fn parameter(&self) -> &str {
        &self.parameter
    }
    pub fn literal(&self) -> u64 {
        self.body.literal
    }
    pub fn body(&self) -> &SourceBody {
        &self.body
    }
    pub fn claim(&self) -> Expr {
        declarations::addition_claim(self.body.reflect(), self.body.literal)
    }
    pub fn proof_candidate(&self) -> Expr {
        Expr::app(declarations::c(declarations::ADEQUACY), self.body.reflect())
    }
}

/// Accept exactly one original safe function, an immutable lexical u64 argument
/// and result, and the tail `argument.wrapping_add(u64 literal)`. No local/imported
/// type alias, binding, trait, macro, attribute, cast or other statement survives.
/// Lexical builtin spelling still is not a Rustc type-resolution certificate.
pub fn project_word64_addition_source(source: &str) -> Result<AdditionSource, Word64AdditionError> {
    let refuse = Word64AdditionError::Unsupported;
    let file = syn::parse_file(source).map_err(|_| refuse("source syntax"))?;
    let [syn::Item::Fn(function)] = file.items.as_slice() else {
        return Err(refuse("requires exactly one original function"));
    };
    let sig = &function.sig;
    let u64_ty = |ty: &syn::Type| matches!(ty, syn::Type::Path(p) if p.qself.is_none() && p.path.is_ident("u64"));
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
        return Err(refuse("requires closed safe nongeneric u64 signature"));
    }
    let Some(syn::FnArg::Typed(arg)) = sig.inputs.first() else {
        return Err(refuse("source argument"));
    };
    let syn::Pat::Ident(binding) = arg.pat.as_ref() else {
        return Err(refuse("argument pattern"));
    };
    if !arg.attrs.is_empty()
        || !binding.attrs.is_empty()
        || binding.by_ref.is_some()
        || binding.mutability.is_some()
        || binding.subpat.is_some()
        || !u64_ty(&arg.ty)
        || !matches!(&sig.output, syn::ReturnType::Type(_,ty) if u64_ty(ty))
    {
        return Err(refuse("requires exact immutable u64 argument and result"));
    }
    let [syn::Stmt::Expr(syn::Expr::MethodCall(call), None)] = function.block.stmts.as_slice()
    else {
        return Err(refuse("requires its one complete wrapping_add tail"));
    };
    if !call.attrs.is_empty()
        || call.method != "wrapping_add"
        || call.turbofish.is_some()
        || call.args.len() != 1
    {
        return Err(refuse("wrapping_add method or arity"));
    }
    let parameter = binding.ident.to_string();
    if !matches!(call.receiver.as_ref(), syn::Expr::Path(p) if p.attrs.is_empty() && p.qself.is_none() && p.path.is_ident(&parameter))
    {
        return Err(refuse("receiver must be the original argument"));
    }
    let Some(syn::Expr::Lit(value)) = call.args.first() else {
        return Err(refuse("requires a checked u64 literal"));
    };
    let syn::Lit::Int(literal) = &value.lit else {
        return Err(refuse("requires an integer literal"));
    };
    if !value.attrs.is_empty() || !matches!(literal.suffix(), "" | "u64") {
        return Err(refuse("literal attributes or suffix"));
    }
    let literal = literal
        .base10_parse::<u64>()
        .map_err(|_| refuse("literal outside u64"))?;
    Ok(AdditionSource {
        source: source.to_owned(),
        function: sig.ident.to_string(),
        parameter,
        body: SourceBody {
            parameter: 0,
            literal,
        },
    })
}
