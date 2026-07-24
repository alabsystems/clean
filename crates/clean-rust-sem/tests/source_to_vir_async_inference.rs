// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for async/await type inference during VIR lowering.

use clean_rust_sem::{LoweredProgram, RustType, SourceProgram, UintType};

fn lowered_program(source: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

#[test]
fn test_block_local_future_await_infers_output() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let result = {
                let future = compute(4u32);
                future.await
            };
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting a block-local future should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_if_future_await_infers_output() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let cond = true;
            let result = (if cond {
                compute(4u32)
            } else {
                compute(5u32)
            }).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an if-expression future should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_match_future_await_infers_output() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let which = 0u32;
            let result = (match which {
                0u32 => compute(4u32),
                _ => compute(5u32),
            }).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting a match-expression future should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_async_closure_call_await_infers_output() {
    let source = r#"
        fn main() -> u32 {
            let compute = async |x: u32| x + 1u32;
            let result = compute(4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an async closure call should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_if_wrapped_async_fn_call_await_infers_output() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let cond = true;
            let callee = if cond { compute } else { compute };
            let result = callee(4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an if-wrapped async callee should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_match_bound_async_fn_item_call_await_infers_output() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let result = match compute {
                callee => callee(4u32).await,
            };
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting a match-bound async callee should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_async_inherent_method_call_await_infers_output() {
    let source = r#"
        struct Counter {}

        impl Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + 1u32
            }
        }

        fn main() -> u32 {
            let counter = Counter {};
            let result = counter.compute(4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an async inherent method should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_async_trait_method_call_await_infers_output() {
    let source = r#"
        trait Worker {
            async fn compute(&self, x: u32) -> u32;
        }

        struct Counter {}

        impl Worker for Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + 1u32
            }
        }

        fn main() -> u32 {
            let counter = Counter {};
            let result = counter.compute(4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an async trait method should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_async_inherent_method_path_call_await_infers_output() {
    let source = r#"
        struct Counter {
            offset: u32,
        }

        impl Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let callee = Counter::compute;
            let result = callee(&counter, 4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an async inherent method path should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_async_trait_method_path_call_await_infers_output() {
    let source = r#"
        trait Worker {
            async fn compute(&self, x: u32) -> u32;
        }

        struct Counter {
            offset: u32,
        }

        impl Worker for Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let callee = <Counter as Worker>::compute;
            let result = callee(&counter, 4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an async trait method path should infer `u32`, got {:?}",
        result_local.ty
    );
}

#[test]
fn test_pin_box_parameter_type_parses_and_lowers() {
    let source = r#"
        struct MyFuture {}

        fn consume_pinned(f: Pin<Box<MyFuture>>) -> u32 {
            42u32
        }

        fn main() -> u32 {
            consume_pinned
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("consume_pinned")
        .expect("lowered program should contain `consume_pinned`");

    let param_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("f"))
        .expect("lowered body should declare `f`");

    // Pin<Box<MyFuture>> should parse as RustType::Pin { inner: Box<Named("MyFuture")> }
    assert!(
        matches!(
            &param_local.ty,
            RustType::Pin { inner } if matches!(
                inner.as_ref(),
                RustType::Box { inner: box_inner } if matches!(
                    box_inner.as_ref(),
                    RustType::Named { name, .. } if name == "MyFuture"
                )
            )
        ),
        "Pin<Box<MyFuture>> should parse as nested Pin/Box/Named, got {:?}",
        param_local.ty
    );
}
