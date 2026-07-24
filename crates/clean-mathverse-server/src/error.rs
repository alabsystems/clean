//! Server error type.
//!
//! Library crate → `thiserror` (the binary wraps these with `anyhow`).

use clean_mathverse::error::MathverseError;

/// Errors raised while loading or serving the Mathverse Core.
#[derive(Debug, thiserror::Error)]
pub enum ServerError {
    /// A shard or index failed to parse / validate.
    #[error("mathverse: {0}")]
    Mathverse(#[from] MathverseError),
    /// Filesystem error while scanning the corpus directory.
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

/// Convenience alias.
pub type ServerResult<T> = Result<T, ServerError>;
