// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Progress reporting utilities for streaming transports

use crate::rpc::RequestId;
use serde_json::Value;
use tokio::sync::mpsc;

/// Progress update payload emitted by handlers
#[derive(Debug, Clone)]
pub struct ProgressUpdate {
    /// Request ID associated with the progress message
    pub request_id: RequestId,
    /// Human-readable progress message
    pub message: String,
    /// Optional percentage (0-100)
    pub percentage: Option<u8>,
    /// Optional structured details
    pub details: Option<Value>,
}

/// Sender used by handlers to emit progress updates
#[derive(Clone, Debug)]
pub struct ProgressSender {
    tx: mpsc::Sender<ProgressUpdate>,
    request_id: RequestId,
}

impl ProgressSender {
    /// Create a new progress sender for the given request
    #[must_use]
    pub fn new(request_id: RequestId, tx: mpsc::Sender<ProgressUpdate>) -> Self {
        Self { tx, request_id }
    }

    /// Send a progress update (async)
    pub async fn notify(
        &self,
        message: impl Into<String>,
        percentage: Option<u8>,
        details: Option<Value>,
    ) {
        let update = ProgressUpdate {
            request_id: self.request_id.clone(),
            message: message.into(),
            percentage: percentage.map(|p| p.min(100)),
            details,
        };

        let _ = self.tx.send(update).await;
    }

    /// Send a progress update (synchronous/blocking)
    ///
    /// This is safe to call from synchronous code (e.g., inside Rayon parallel loops).
    /// Uses `try_send` to avoid blocking if the channel is full.
    pub fn notify_sync(
        &self,
        message: impl Into<String>,
        percentage: Option<u8>,
        details: Option<Value>,
    ) {
        let update = ProgressUpdate {
            request_id: self.request_id.clone(),
            message: message.into(),
            percentage: percentage.map(|p| p.min(100)),
            details,
        };

        // Use try_send to avoid blocking in sync context
        let _ = self.tx.try_send(update);
    }

    /// Get the underlying channel sender for passing to synchronous contexts
    ///
    /// This allows synchronous code to create ProgressUpdate objects and send them directly.
    #[must_use]
    pub fn tx(&self) -> &mpsc::Sender<ProgressUpdate> {
        &self.tx
    }

    /// Get the request ID
    #[must_use]
    pub fn request_id(&self) -> &RequestId {
        &self.request_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_progress_update_fields() {
        let update = ProgressUpdate {
            request_id: RequestId::Number(42),
            message: "Processing...".to_string(),
            percentage: Some(50),
            details: Some(serde_json::json!({"step": 3})),
        };

        assert_eq!(update.request_id, RequestId::Number(42));
        assert_eq!(update.message, "Processing...");
        assert_eq!(update.percentage, Some(50));
        assert!(
            update.details.is_some(),
            "details should be set, got: {:?}",
            update.details
        );
    }

    #[test]
    fn test_progress_update_no_percentage() {
        let update = ProgressUpdate {
            request_id: RequestId::String("req-123".into()),
            message: "Starting".to_string(),
            percentage: None,
            details: None,
        };

        assert_eq!(update.request_id, RequestId::String("req-123".into()));
        assert_eq!(update.message, "Starting");
        assert_eq!(update.percentage, None, "percentage should be None");
        assert_eq!(update.details, None, "details should be None");
    }

    #[test]
    fn test_progress_update_clone() {
        let update = ProgressUpdate {
            request_id: RequestId::Number(1),
            message: "Test".to_string(),
            percentage: Some(75),
            details: None,
        };

        let cloned = update.clone();
        assert_eq!(cloned.request_id, update.request_id);
        assert_eq!(cloned.message, update.message);
        assert_eq!(cloned.percentage, update.percentage);
    }

    #[test]
    fn test_progress_update_debug() {
        let update = ProgressUpdate {
            request_id: RequestId::Null,
            message: "Debug test".to_string(),
            percentage: Some(100),
            details: None,
        };

        let debug_str = format!("{update:?}");
        assert!(debug_str.contains("ProgressUpdate"));
        assert!(debug_str.contains("Debug test"));
    }

    #[tokio::test]
    async fn test_progress_sender_new() {
        let (tx, _rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(42), tx);

        // ProgressSender should be clonable
        let _cloned = sender.clone();
    }

    #[tokio::test]
    async fn test_progress_sender_notify_basic() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        sender.notify("Testing", Some(50), None).await;

        let received = rx.recv().await.expect("Should receive update");
        assert_eq!(received.request_id, RequestId::Number(1));
        assert_eq!(received.message, "Testing");
        assert_eq!(received.percentage, Some(50));
        assert_eq!(
            received.details, None,
            "basic notify should have no details"
        );
    }

    #[tokio::test]
    async fn test_progress_sender_notify_with_details() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::String("test".into()), tx);

        let details = serde_json::json!({"items_processed": 10, "total_items": 100});
        sender
            .notify("Processing batch", Some(10), Some(details))
            .await;

        let received = rx.recv().await.expect("Should receive update");
        assert_eq!(received.request_id, RequestId::String("test".into()));
        assert_eq!(received.message, "Processing batch");
        assert_eq!(received.percentage, Some(10));
        let details = received
            .details
            .expect("notify with details should preserve them");
        assert_eq!(details["items_processed"], 10);
        assert_eq!(details["total_items"], 100);
    }

    #[tokio::test]
    async fn test_progress_sender_percentage_clamped_to_100() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        // Send percentage > 100, should be clamped to 100
        sender.notify("Done", Some(150), None).await;

        let received = rx.recv().await.expect("Should receive update");
        assert_eq!(received.percentage, Some(100));
    }

    #[tokio::test]
    async fn test_progress_sender_multiple_updates() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        sender.notify("Step 1", Some(25), None).await;
        sender.notify("Step 2", Some(50), None).await;
        sender.notify("Step 3", Some(75), None).await;
        sender.notify("Done", Some(100), None).await;

        let mut messages = Vec::new();
        while let Ok(update) = rx.try_recv() {
            messages.push(update.message);
        }

        assert_eq!(messages, vec!["Step 1", "Step 2", "Step 3", "Done"]);
    }

    #[tokio::test]
    async fn test_progress_sender_handles_closed_channel() {
        let (tx, rx) = mpsc::channel::<ProgressUpdate>(1);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        // Drop receiver to close channel
        drop(rx);

        // notify should not panic when channel is closed (it ignores the send error)
        sender.notify("After close", Some(50), None).await;
        // Test passes if no panic occurs
    }

    #[tokio::test]
    async fn test_progress_sender_debug() {
        let (tx, _rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(42), tx);

        let debug_str = format!("{sender:?}");
        assert!(debug_str.contains("ProgressSender"));
    }

    #[tokio::test]
    async fn test_progress_sender_notify_sync_basic() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        // notify_sync should work from any context
        sender.notify_sync("Sync test", Some(50), None);

        let received = rx.recv().await.expect("Should receive update");
        assert_eq!(received.request_id, RequestId::Number(1));
        assert_eq!(received.message, "Sync test");
        assert_eq!(received.percentage, Some(50));
    }

    #[tokio::test]
    async fn test_progress_sender_notify_sync_with_details() {
        let (tx, mut rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::String("sync-req".into()), tx);

        let details = serde_json::json!({"item": "test", "count": 42});
        sender.notify_sync("Processing item", Some(25), Some(details));

        let received = rx.recv().await.expect("Should receive update");
        assert_eq!(received.message, "Processing item");
        let details_ref = received
            .details
            .as_ref()
            .expect("sync notify with details should preserve them");
        assert_eq!(details_ref["item"], "test");
    }

    #[tokio::test]
    async fn test_progress_sender_request_id() {
        let (tx, _rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(42), tx);

        assert_eq!(sender.request_id(), &RequestId::Number(42));
    }

    #[tokio::test]
    async fn test_progress_sender_tx_accessor() {
        let (tx, _rx) = mpsc::channel::<ProgressUpdate>(8);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        // Should be able to access the underlying sender
        let _tx_ref = sender.tx();
        // Just verify it compiles and returns the reference
    }

    #[test]
    fn test_progress_sender_notify_sync_non_blocking() {
        // Test that notify_sync doesn't block when channel is full
        let (tx, _rx) = mpsc::channel::<ProgressUpdate>(1);
        let sender = ProgressSender::new(RequestId::Number(1), tx);

        // Fill the channel
        sender.notify_sync("First", None, None);
        // This should not block even though channel is full (uses try_send)
        sender.notify_sync("Second", None, None);
        // Test passes if no deadlock/hang occurs
    }
}
