// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ML tensor semantics formalization
//!
//! Validates that the tensor type system, NN operations, and IBP soundness
//! axioms are correctly registered in the environment.

use super::*;

#[test]
fn test_tensor_ml_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_tensor_ml());
    env.init_tensor_ml().unwrap();
    assert!(env.has_tensor_ml());
}

#[test]
fn test_tensor_ml_idempotent() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();
    env.init_tensor_ml().unwrap();
    assert!(env.has_tensor_ml());
}

#[test]
fn test_tensor_ml_types_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.DType",
        "ML.TensorSemantics.float32",
        "ML.TensorSemantics.float64",
        "ML.TensorSemantics.int32",
        "ML.TensorSemantics.int64",
        "ML.TensorSemantics.Shape",
        "ML.TensorSemantics.Tensor",
        "ML.TensorSemantics.Scalar",
        "ML.TensorSemantics.rank",
        "ML.TensorSemantics.numel",
        "ML.TensorSemantics.shape_eq_dec",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_float32_semantics_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.Float32",
        "ML.TensorSemantics.float32_add",
        "ML.TensorSemantics.float32_mul",
        "ML.TensorSemantics.float32_neg",
        "ML.TensorSemantics.float32_div",
        "ML.TensorSemantics.float32_le",
        "ML.TensorSemantics.float32_lt",
        "ML.TensorSemantics.float32_abs",
        "ML.TensorSemantics.float32_exp",
        "ML.TensorSemantics.float32_nan",
        "ML.TensorSemantics.float32_inf",
        "ML.TensorSemantics.float32_is_nan",
        "ML.TensorSemantics.float32_is_finite",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_matmul_properties_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.matmul",
        "ML.TensorSemantics.matmul_assoc",
        "ML.TensorSemantics.matmul_add_left",
        "ML.TensorSemantics.matmul_add_right",
        "ML.TensorSemantics.matmul_scalar",
        "ML.TensorSemantics.matmul_transpose",
        "ML.TensorSemantics.matmul_identity",
        "ML.TensorSemantics.bmm",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_conv_operations_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.conv1d",
        "ML.TensorSemantics.conv2d",
        "ML.TensorSemantics.conv1d_output_size",
        "ML.TensorSemantics.conv2d_output_size",
        "ML.TensorSemantics.conv2d_as_matmul",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_activations_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.relu",
        "ML.TensorSemantics.relu_idempotent",
        "ML.TensorSemantics.relu_nonneg",
        "ML.TensorSemantics.relu_monotone",
        "ML.TensorSemantics.sigmoid",
        "ML.TensorSemantics.sigmoid_range",
        "ML.TensorSemantics.sigmoid_monotone",
        "ML.TensorSemantics.tanh",
        "ML.TensorSemantics.tanh_range",
        "ML.TensorSemantics.gelu",
        "ML.TensorSemantics.leaky_relu",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_normalization_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.softmax",
        "ML.TensorSemantics.softmax_nonneg",
        "ML.TensorSemantics.softmax_sum_one",
        "ML.TensorSemantics.softmax_monotone",
        "ML.TensorSemantics.log_softmax",
        "ML.TensorSemantics.layer_norm",
        "ML.TensorSemantics.layer_norm_zero_mean",
        "ML.TensorSemantics.layer_norm_unit_var",
        "ML.TensorSemantics.instance_norm",
        "ML.TensorSemantics.batch_norm",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_ibp_soundness_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.IntervalBound",
        "ML.TensorSemantics.interval_valid",
        "ML.TensorSemantics.ibp_contains",
        "ML.TensorSemantics.ibp_relu",
        "ML.TensorSemantics.ibp_relu_sound",
        "ML.TensorSemantics.ibp_linear",
        "ML.TensorSemantics.ibp_linear_sound",
        "ML.TensorSemantics.ibp_conv",
        "ML.TensorSemantics.ibp_conv_sound",
        "ML.TensorSemantics.ibp_sigmoid",
        "ML.TensorSemantics.ibp_sigmoid_sound",
        "ML.TensorSemantics.ibp_composition",
        "ML.TensorSemantics.ibp_composition_sound",
        "ML.TensorSemantics.ibp_network_sound",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_proof_certificate_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.ProofCertificate",
        "ML.TensorSemantics.CertKind",
        "ML.TensorSemantics.cert_valid",
        "ML.TensorSemantics.cert_property",
        "ML.TensorSemantics.cert_verify",
        "ML.TensorSemantics.cert_verify_sound",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_network_composition_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.Layer",
        "ML.TensorSemantics.Network",
        "ML.TensorSemantics.network_eval",
        "ML.TensorSemantics.network_compose",
        "ML.TensorSemantics.network_compose_assoc",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_lipschitz_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.lipschitz",
        "ML.TensorSemantics.relu_lipschitz",
        "ML.TensorSemantics.linear_lipschitz",
        "ML.TensorSemantics.compose_lipschitz",
        "ML.TensorSemantics.network_lipschitz",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_element_ops_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.tensor_add",
        "ML.TensorSemantics.tensor_sub",
        "ML.TensorSemantics.tensor_mul",
        "ML.TensorSemantics.tensor_div",
        "ML.TensorSemantics.tensor_neg",
        "ML.TensorSemantics.tensor_abs",
        "ML.TensorSemantics.tensor_scalar_mul",
        "ML.TensorSemantics.tensor_index",
        "ML.TensorSemantics.tensor_reshape",
        "ML.TensorSemantics.tensor_transpose",
        "ML.TensorSemantics.tensor_flatten",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_pooling_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.max_pool2d",
        "ML.TensorSemantics.avg_pool2d",
        "ML.TensorSemantics.adaptive_avg_pool",
        "ML.TensorSemantics.max_pool_monotone",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_sequence_ops_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.embedding",
        "ML.TensorSemantics.embedding_as_matmul",
        "ML.TensorSemantics.lstm_cell",
        "ML.TensorSemantics.lstm",
        "ML.TensorSemantics.attention",
        "ML.TensorSemantics.multi_head_attention",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_loss_functions_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.cross_entropy",
        "ML.TensorSemantics.cross_entropy_nonneg",
        "ML.TensorSemantics.mse_loss",
        "ML.TensorSemantics.mse_loss_nonneg",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_dim_compat_exist() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();

    let constants = vec![
        "ML.TensorSemantics.DimCompat",
        "ML.TensorSemantics.broadcast_compat",
        "ML.TensorSemantics.matmul_compat",
        "ML.TensorSemantics.conv_compat",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_tensor_ml_depends_on_linear_algebra() {
    let mut env = Environment::new();
    env.init_tensor_ml().unwrap();
    // init_tensor_ml should have pulled in algebra_linear as a dependency
    assert!(env.has_algebra_linear());
}
