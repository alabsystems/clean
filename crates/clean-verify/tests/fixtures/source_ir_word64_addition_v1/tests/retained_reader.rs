use super::*;

// Raw Expr is untrusted data. JSON's fixed128 container depth is too small for
// this already retained three-step proof; use the canonical kernel's scoped
// resource accountant instead. No checking metadata or proof authority restores.
fn decode_retained_expr(
    bytes: &[u8],
    limits: clean_kernel::DecodeResourceLimits,
) -> Result<Expr, String> {
    use serde::Deserialize;
    if bytes.len() > 8 * 1024 * 1024 {
        return Err("retained expression byte limit".into());
    }
    clean_kernel::with_decode_resource_limits(limits, || {
        let mut de = serde_json::Deserializer::from_slice(bytes);
        de.disable_recursion_limit();
        let term = Expr::deserialize(&mut de).map_err(|e| e.to_string())?;
        de.end().map_err(|e| e.to_string())?;
        Ok(term)
    })
}
pub(super) fn read_retained_expr(path: &std::path::Path) -> Expr {
    decode_retained_expr(
        &std::fs::read(path).unwrap(),
        clean_kernel::DecodeResourceLimits {
            max_nodes: 1_000_000,
            max_depth: 512,
        },
    )
    .unwrap()
}
#[test]
fn retained_decode_resource_scope_refuses_zero_population_and_trailing_bytes() {
    let b = serde_json::to_vec(&nat(7)).unwrap();
    assert!(decode_retained_expr(
        &b,
        clean_kernel::DecodeResourceLimits {
            max_nodes: 0,
            max_depth: 512
        }
    )
    .is_err());
    let mut extra = b.clone();
    extra.extend_from_slice(b" null");
    assert!(decode_retained_expr(
        &extra,
        clean_kernel::DecodeResourceLimits {
            max_nodes: 1_000_000,
            max_depth: 512
        }
    )
    .is_err());
    let nested = Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(0));
    assert!(decode_retained_expr(
        &serde_json::to_vec(&nested).unwrap(),
        clean_kernel::DecodeResourceLimits {
            max_nodes: 1_000_000,
            max_depth: 1
        }
    )
    .is_err());
}
