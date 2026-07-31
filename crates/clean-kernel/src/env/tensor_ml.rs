// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ML tensor semantics formalization for Environment
//!
//! This module formalizes tensor types and operations for machine learning
//! proof certificates. It provides the mathematical foundation for mly's
//! proof-carrying ML models, enabling clean to serve as the trusted proof
//! checker for neural network verification.
//!
//! Reference: TorchLean (arXiv:2602.22631) for prior art formalizing NN
//! semantics in Lean 4.
//!
//! Key concepts:
//! - Tensor types with rank, dtype, and shape tracking
//! - Core NN operations (matmul, conv, activation functions)
//! - Dimension compatibility constraints
//! - Interval bound propagation (IBP) soundness
//! - IEEE 754 float semantics (binary32)
//!
//! Cross-repo dependency: mly (alabsystems/mly)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Register a batch of axiom declarations under a shared universe parameter.
fn register_axioms(
    env: &mut Environment,
    names: &[&str],
    u: &Name,
    type_u: &Expr,
) -> Result<(), EnvError> {
    for name in names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![u.clone()],
            type_: type_u.clone(),
        })?;
    }
    Ok(())
}

/// Tensor types: DType, Shape, Tensor, Scalar, rank, numel.
const TENSOR_TYPES: &[&str] = &[
    "ML.TensorSemantics.DType",        // DType: float32, float64, int32, etc.
    "ML.TensorSemantics.float32",      // IEEE 754 binary32
    "ML.TensorSemantics.float64",      // IEEE 754 binary64
    "ML.TensorSemantics.int32",        // 32-bit signed integer
    "ML.TensorSemantics.int64",        // 64-bit signed integer
    "ML.TensorSemantics.Shape",        // Shape : List Nat (dimension list)
    "ML.TensorSemantics.Tensor",       // Tensor dtype shape : Type
    "ML.TensorSemantics.Scalar",       // Scalar dtype : Type (0-d tensor)
    "ML.TensorSemantics.rank",         // rank : Shape -> Nat
    "ML.TensorSemantics.numel",        // numel : Shape -> Nat (total elements)
    "ML.TensorSemantics.shape_eq_dec", // DecidableEq Shape
];

/// IEEE 754 binary32 float semantics.
const FLOAT32_SEMANTICS: &[&str] = &[
    "ML.TensorSemantics.Float32",           // Float32 : Type
    "ML.TensorSemantics.float32_add",       // (+) : Float32 -> Float32 -> Float32
    "ML.TensorSemantics.float32_mul",       // (*) : Float32 -> Float32 -> Float32
    "ML.TensorSemantics.float32_neg",       // (-) : Float32 -> Float32
    "ML.TensorSemantics.float32_div",       // (/) : Float32 -> Float32 -> Float32
    "ML.TensorSemantics.float32_le",        // (<=) : Float32 -> Float32 -> Prop
    "ML.TensorSemantics.float32_lt",        // (<) : Float32 -> Float32 -> Prop
    "ML.TensorSemantics.float32_abs",       // abs : Float32 -> Float32
    "ML.TensorSemantics.float32_exp",       // exp : Float32 -> Float32
    "ML.TensorSemantics.float32_sqrt",      // sqrt : Float32 -> Float32
    "ML.TensorSemantics.float32_of_nat",    // Float32.ofNat : Nat -> Float32
    "ML.TensorSemantics.float32_of_rat",    // Float32.ofRat : Rat -> Float32
    "ML.TensorSemantics.float32_nan",       // NaN : Float32
    "ML.TensorSemantics.float32_inf",       // +inf : Float32
    "ML.TensorSemantics.float32_neg_inf",   // -inf : Float32
    "ML.TensorSemantics.float32_is_nan",    // isNaN : Float32 -> Prop
    "ML.TensorSemantics.float32_is_finite", // isFinite : Float32 -> Prop
];

/// Core tensor operations: element-wise, indexing, reshaping.
const TENSOR_OPS: &[&str] = &[
    "ML.TensorSemantics.tensor_add",        // (+) element-wise
    "ML.TensorSemantics.tensor_sub",        // (-) element-wise
    "ML.TensorSemantics.tensor_mul",        // (*) element-wise
    "ML.TensorSemantics.tensor_div",        // (/) element-wise
    "ML.TensorSemantics.tensor_neg",        // neg element-wise
    "ML.TensorSemantics.tensor_abs",        // abs element-wise
    "ML.TensorSemantics.tensor_scalar_mul", // scalar * tensor
    "ML.TensorSemantics.tensor_index",      // index into tensor
    "ML.TensorSemantics.tensor_reshape",    // reshape preserving numel
    "ML.TensorSemantics.tensor_transpose",  // transpose last two dims
    "ML.TensorSemantics.tensor_flatten",    // flatten to 1-d
    "ML.TensorSemantics.tensor_squeeze",    // remove dims of size 1
    "ML.TensorSemantics.tensor_unsqueeze",  // add dim of size 1
];

/// Matrix multiplication and convolution operations with algebraic properties.
const MATMUL_CONV: &[&str] = &[
    "ML.TensorSemantics.matmul",             // [m,k] x [k,n] -> [m,n]
    "ML.TensorSemantics.matmul_assoc",       // associativity
    "ML.TensorSemantics.matmul_add_left",    // left distributivity
    "ML.TensorSemantics.matmul_add_right",   // right distributivity
    "ML.TensorSemantics.matmul_scalar",      // scalar commutes
    "ML.TensorSemantics.matmul_transpose",   // transpose reverses
    "ML.TensorSemantics.matmul_identity",    // identity element
    "ML.TensorSemantics.bmm",                // batched matmul
    "ML.TensorSemantics.conv1d",             // 1-d convolution
    "ML.TensorSemantics.conv2d",             // 2-d convolution
    "ML.TensorSemantics.conv1d_output_size", // output size formula
    "ML.TensorSemantics.conv2d_output_size", // output size formula
    "ML.TensorSemantics.conv2d_as_matmul",   // conv = im2col + matmul
];

/// Activation functions and their mathematical properties.
const ACTIVATIONS: &[&str] = &[
    "ML.TensorSemantics.relu",             // max(0, x)
    "ML.TensorSemantics.relu_idempotent",  // relu . relu = relu
    "ML.TensorSemantics.relu_nonneg",      // relu x >= 0
    "ML.TensorSemantics.relu_monotone",    // monotonicity
    "ML.TensorSemantics.sigmoid",          // 1 / (1 + exp(-x))
    "ML.TensorSemantics.sigmoid_range",    // 0 < sigmoid x < 1
    "ML.TensorSemantics.sigmoid_monotone", // monotonicity
    "ML.TensorSemantics.tanh",             // hyperbolic tangent
    "ML.TensorSemantics.tanh_range",       // -1 < tanh x < 1
    "ML.TensorSemantics.gelu",             // x * Phi(x)
    "ML.TensorSemantics.leaky_relu",       // max(alpha*x, x)
];

/// Normalization layers, pooling, embedding, sequence ops, and loss functions.
const LAYERS_AND_LOSS: &[&str] = &[
    "ML.TensorSemantics.softmax",              // softmax normalization
    "ML.TensorSemantics.softmax_nonneg",       // non-negativity
    "ML.TensorSemantics.softmax_sum_one",      // sums to 1
    "ML.TensorSemantics.softmax_monotone",     // order preserving
    "ML.TensorSemantics.log_softmax",          // log(softmax x)
    "ML.TensorSemantics.layer_norm",           // layer normalization
    "ML.TensorSemantics.layer_norm_zero_mean", // zero mean
    "ML.TensorSemantics.layer_norm_unit_var",  // unit variance
    "ML.TensorSemantics.instance_norm",        // instance normalization
    "ML.TensorSemantics.batch_norm",           // batch normalization
    "ML.TensorSemantics.max_pool2d",           // max pooling 2-d
    "ML.TensorSemantics.avg_pool2d",           // average pooling 2-d
    "ML.TensorSemantics.adaptive_avg_pool",    // adaptive average pool
    "ML.TensorSemantics.max_pool_monotone",    // pooling monotonicity
    "ML.TensorSemantics.embedding",            // embedding lookup
    "ML.TensorSemantics.embedding_as_matmul",  // one_hot @ W
    "ML.TensorSemantics.lstm_cell",            // LSTM single step
    "ML.TensorSemantics.lstm",                 // LSTM unrolled
    "ML.TensorSemantics.attention",            // scaled dot-product attention
    "ML.TensorSemantics.multi_head_attention", // multi-head attention
    "ML.TensorSemantics.cross_entropy",        // cross-entropy loss
    "ML.TensorSemantics.cross_entropy_nonneg", // non-negativity
    "ML.TensorSemantics.mse_loss",             // mean squared error
    "ML.TensorSemantics.mse_loss_nonneg",      // non-negativity
];

/// Dimension compatibility, IBP soundness, certificates, network composition, Lipschitz.
const VERIFICATION: &[&str] = &[
    "ML.TensorSemantics.DimCompat",             // shape compatibility
    "ML.TensorSemantics.broadcast_compat",      // broadcasting
    "ML.TensorSemantics.matmul_compat",         // matmul shape check
    "ML.TensorSemantics.conv_compat",           // conv shape check
    "ML.TensorSemantics.IntervalBound",         // (lower, upper) pair
    "ML.TensorSemantics.interval_valid",        // lower <= upper
    "ML.TensorSemantics.ibp_contains",          // containment predicate
    "ML.TensorSemantics.ibp_relu",              // IBP through relu
    "ML.TensorSemantics.ibp_relu_sound",        // relu IBP soundness
    "ML.TensorSemantics.ibp_linear",            // IBP through linear
    "ML.TensorSemantics.ibp_linear_sound",      // linear IBP soundness
    "ML.TensorSemantics.ibp_conv",              // IBP through conv
    "ML.TensorSemantics.ibp_conv_sound",        // conv IBP soundness
    "ML.TensorSemantics.ibp_sigmoid",           // IBP through sigmoid
    "ML.TensorSemantics.ibp_sigmoid_sound",     // sigmoid IBP soundness
    "ML.TensorSemantics.ibp_composition",       // IBP composition
    "ML.TensorSemantics.ibp_composition_sound", // composition soundness
    "ML.TensorSemantics.ibp_network_sound",     // top-level network soundness
    "ML.TensorSemantics.ProofCertificate",      // certificate type
    "ML.TensorSemantics.CertKind",              // kani | gamma_crown | ay | fusion
    "ML.TensorSemantics.cert_valid",            // validity predicate
    "ML.TensorSemantics.cert_property",         // certified property
    "ML.TensorSemantics.cert_verify",           // verification function
    "ML.TensorSemantics.cert_verify_sound",     // verify true -> valid
    "ML.TensorSemantics.Layer",                 // layer type
    "ML.TensorSemantics.Network",               // network as layer list
    "ML.TensorSemantics.network_eval",          // evaluate network
    "ML.TensorSemantics.network_compose",       // compose networks
    "ML.TensorSemantics.network_compose_assoc", // associativity
    "ML.TensorSemantics.lipschitz",             // Lipschitz predicate
    "ML.TensorSemantics.relu_lipschitz",        // relu is 1-Lipschitz
    "ML.TensorSemantics.linear_lipschitz",      // operator norm bound
    "ML.TensorSemantics.compose_lipschitz",     // product of constants
    "ML.TensorSemantics.network_lipschitz",     // network bound
];

impl Environment {
    /// Initialize ML.TensorSemantics module
    ///
    /// Provides axioms for tensor types, neural network operations, and
    /// verification conditions used by mly proof certificates.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.tensor_ml_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_tensor_ml(&mut self) -> Result<(), EnvError> {
        if self.tensor_ml_init {
            return Ok(());
        }

        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_field()?;
        self.init_algebra_linear()?;

        let u = Name::from_string("u");
        let type_u = Expr::sort(Level::succ(Level::param(u.clone())));

        register_axioms(self, TENSOR_TYPES, &u, &type_u)?;
        register_axioms(self, FLOAT32_SEMANTICS, &u, &type_u)?;
        register_axioms(self, TENSOR_OPS, &u, &type_u)?;
        register_axioms(self, MATMUL_CONV, &u, &type_u)?;
        register_axioms(self, ACTIVATIONS, &u, &type_u)?;
        register_axioms(self, LAYERS_AND_LOSS, &u, &type_u)?;
        register_axioms(self, VERIFICATION, &u, &type_u)?;

        self.tensor_ml_init = true;
        Ok(())
    }

    /// Check if ML.TensorSemantics has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `init_tensor_ml` has completed successfully
    #[cfg(test)]
    pub(crate) fn has_tensor_ml(&self) -> bool {
        self.tensor_ml_init
    }
}
