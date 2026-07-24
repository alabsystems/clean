// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON-RPC 2.0 protocol handling
//!
//! Implements the JSON-RPC 2.0 specification for the clean server.
//! See: <https://www.jsonrpc.org/specification>

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// JSON-RPC version string
pub const JSONRPC_VERSION: &str = "2.0";

/// JSON-RPC request ID (string, number, or null).
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RequestId {
    /// Null ID (used when a response must carry an explicit `null` identifier).
    ///
    /// For requests, a `null` id is treated as missing and may be skipped on
    /// serialization.
    #[default]
    Null,
    /// Numeric request ID (JSON integer).
    ///
    /// JSON-RPC permits numbers, but this implementation restricts IDs to i64.
    ///
    /// Serialized as a JSON number.
    Number(i64),
    /// String request ID (JSON string).
    ///
    /// Serialized as a JSON string.
    String(String),
}

/// JSON-RPC 2.0 request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
    /// Protocol version (must be "2.0")
    pub jsonrpc: String,
    /// Method name
    pub method: String,
    /// Parameters (optional)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
    /// Request ID (None for notifications)
    #[serde(default, skip_serializing_if = "is_null_id")]
    pub id: Option<RequestId>,
}

fn is_null_id(id: &Option<RequestId>) -> bool {
    matches!(id, None | Some(RequestId::Null))
}

impl Request {
    /// Create a new request
    pub fn new(method: impl Into<String>, params: Option<Value>, id: RequestId) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION.to_string(),
            method: method.into(),
            params,
            id: Some(id),
        }
    }

    /// Create a notification (no id, no response expected)
    pub fn notification(method: impl Into<String>, params: Option<Value>) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION.to_string(),
            method: method.into(),
            params,
            id: None,
        }
    }

    /// Check if this is a notification (no response expected; id missing or null)
    #[must_use]
    pub fn is_notification(&self) -> bool {
        matches!(self.id, None | Some(RequestId::Null))
    }
}

/// JSON-RPC 2.0 response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Response {
    /// Protocol version (must be "2.0")
    pub jsonrpc: String,
    /// Result (on success)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    /// Error (on failure)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<RpcError>,
    /// Request ID (same as request, null for errors without id)
    pub id: RequestId,
}

impl Response {
    /// Create a success response
    #[must_use]
    pub fn success(id: RequestId, result: Value) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION.to_string(),
            result: Some(result),
            error: None,
            id,
        }
    }

    /// Create an error response
    #[must_use]
    pub fn error(id: RequestId, error: RpcError) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION.to_string(),
            result: None,
            error: Some(error),
            id,
        }
    }

    /// Create a success response from a serializable value
    pub fn success_typed<T: Serialize>(
        id: RequestId,
        result: &T,
    ) -> Result<Self, serde_json::Error> {
        Ok(Self::success(id, serde_json::to_value(result)?))
    }
}

/// JSON-RPC 2.0 error object
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcError {
    /// Error code
    pub code: i32,
    /// Error message
    pub message: String,
    /// Additional data (optional)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

/// Standard JSON-RPC error codes
pub mod error_codes {
    /// Parse error: Invalid JSON was received
    pub const PARSE_ERROR: i32 = -32700;
    /// Invalid Request: The JSON sent is not a valid Request object
    pub const INVALID_REQUEST: i32 = -32600;
    /// Method not found: The method does not exist
    pub const METHOD_NOT_FOUND: i32 = -32601;
    /// Invalid params: Invalid method parameter(s)
    pub const INVALID_PARAMS: i32 = -32602;
    /// Internal error: Internal JSON-RPC error
    pub const INTERNAL_ERROR: i32 = -32603;

    // Server error: Reserved for implementation-defined server-errors (-32000 to -32099)

    /// Type checking error
    pub const TYPE_ERROR: i32 = -32000;
    /// Parse error (Lean syntax)
    pub const LEAN_PARSE_ERROR: i32 = -32001;
    /// Elaboration error
    pub const ELABORATION_ERROR: i32 = -32002;
    /// Proof search failed
    pub const PROOF_NOT_FOUND: i32 = -32003;
    /// Timeout
    pub const TIMEOUT: i32 = -32004;
    /// Per-connection request limit exceeded
    pub const REQUEST_LIMIT_EXCEEDED: i32 = -32005;
}

impl RpcError {
    /// Create a new error
    pub fn new(code: i32, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            data: None,
        }
    }

    /// Create an error with additional data
    pub fn with_data(code: i32, message: impl Into<String>, data: Value) -> Self {
        Self {
            code,
            message: message.into(),
            data: Some(data),
        }
    }

    /// Parse error
    #[must_use]
    pub fn parse_error(details: impl Into<String>) -> Self {
        Self::new(error_codes::PARSE_ERROR, details)
    }

    /// Invalid request
    #[must_use]
    pub fn invalid_request(details: impl Into<String>) -> Self {
        Self::new(error_codes::INVALID_REQUEST, details)
    }

    /// Method not found
    #[must_use]
    pub fn method_not_found(method: &str) -> Self {
        Self::new(
            error_codes::METHOD_NOT_FOUND,
            format!("Method not found: {method}"),
        )
    }

    /// Invalid params
    #[must_use]
    pub fn invalid_params(details: impl Into<String>) -> Self {
        Self::new(error_codes::INVALID_PARAMS, details)
    }

    /// Internal error
    #[must_use]
    pub fn internal_error(details: impl Into<String>) -> Self {
        Self::new(error_codes::INTERNAL_ERROR, details)
    }

    /// Type error
    #[must_use]
    pub fn type_error(details: impl Into<String>) -> Self {
        Self::new(error_codes::TYPE_ERROR, details)
    }

    /// Parse error (Lean)
    #[must_use]
    pub fn lean_parse_error(details: impl Into<String>) -> Self {
        Self::new(error_codes::LEAN_PARSE_ERROR, details)
    }

    /// Elaboration error
    #[must_use]
    pub fn elaboration_error(details: impl Into<String>) -> Self {
        Self::new(error_codes::ELABORATION_ERROR, details)
    }

    /// Proof not found
    #[must_use]
    pub fn proof_not_found() -> Self {
        Self::new(error_codes::PROOF_NOT_FOUND, "Proof search failed")
    }

    /// Timeout
    #[must_use]
    pub fn timeout(timeout_ms: u64) -> Self {
        Self::new(
            error_codes::TIMEOUT,
            format!("Operation timed out after {timeout_ms}ms"),
        )
    }

    /// Per-connection request limit exceeded
    #[must_use]
    pub fn request_limit_exceeded(limit: u64) -> Self {
        Self::new(
            error_codes::REQUEST_LIMIT_EXCEEDED,
            format!("Per-connection request limit exceeded ({limit})"),
        )
    }
}

/// Batch request (array of requests)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(transparent)]
pub struct BatchRequest(pub Vec<Request>);

/// Batch response (array of responses)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(transparent)]
pub struct BatchResponse(pub Vec<Response>);

/// Parsed batch item (request or error).
#[derive(Debug, Clone)]
pub enum BatchItem {
    /// A successfully parsed JSON-RPC request from a batch element.
    ///
    /// These items pass basic validation (currently JSON-RPC version checks).
    Request(Request),
    /// A parse or validation error for this batch element (maps to an error response).
    ///
    /// Used to build the corresponding error response while preserving ordering.
    Error(RpcError),
}

impl BatchItem {
    fn from_value(value: Value) -> Self {
        if !value.is_object() {
            return BatchItem::Error(RpcError::invalid_request(
                "Invalid request in batch: expected object",
            ));
        }
        let req: Request = match serde_json::from_value(value) {
            Ok(req) => req,
            Err(e) => {
                return BatchItem::Error(RpcError::invalid_request(format!(
                    "Invalid request in batch: {e}"
                )));
            }
        };
        if let Err(err) = validate_request(&req) {
            return BatchItem::Error(err);
        }
        BatchItem::Request(req)
    }
}

fn validate_request(req: &Request) -> Result<(), RpcError> {
    if req.jsonrpc != JSONRPC_VERSION {
        return Err(RpcError::invalid_request(format!(
            "Invalid jsonrpc version: {}",
            req.jsonrpc
        )));
    }
    Ok(())
}

/// Parse a JSON-RPC message (single or batch)
pub fn parse_message(json: &str) -> Result<ParsedMessage, RpcError> {
    // First, try to parse as valid JSON
    let value: Value = serde_json::from_str(json)
        .map_err(|e| RpcError::parse_error(format!("Invalid JSON: {e}")))?;

    // Check if it's a batch (array) or single request (object)
    match value {
        Value::Array(arr) => {
            if arr.is_empty() {
                return Err(RpcError::invalid_request("Empty batch request"));
            }
            let items = arr.into_iter().map(BatchItem::from_value).collect();
            Ok(ParsedMessage::Batch(items))
        }
        Value::Object(_) => {
            let req: Request = serde_json::from_value(value)
                .map_err(|e| RpcError::invalid_request(format!("Invalid request: {e}")))?;
            validate_request(&req)?;
            Ok(ParsedMessage::Single(req))
        }
        _ => Err(RpcError::invalid_request(
            "Request must be an object or array",
        )),
    }
}

/// Parsed message (single or batch).
#[derive(Debug, Clone)]
pub enum ParsedMessage {
    /// A single JSON-RPC request or notification.
    ///
    /// Represents a non-array JSON-RPC payload.
    Single(Request),
    /// A batch of JSON-RPC requests (array in the protocol).
    ///
    /// Each element is parsed independently into a request or error item.
    Batch(Vec<BatchItem>),
}

#[cfg(test)]
#[path = "rpc_tests.rs"]
mod tests;
