// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory hierarchical names.

use std::fmt;

/// OpenTheory hierarchical name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OtName {
    pub namespace: Vec<String>,
    pub component: String,
}

impl OtName {
    #[must_use]
    pub fn new(namespace: Vec<String>, component: impl Into<String>) -> Self {
        Self {
            namespace,
            component: component.into(),
        }
    }

    #[must_use]
    pub fn global(component: impl Into<String>) -> Self {
        Self::new(Vec::new(), component)
    }

    #[must_use]
    pub fn is_global(&self) -> bool {
        self.namespace.is_empty()
    }

    #[must_use]
    pub fn with_component(&self, component: impl Into<String>) -> Self {
        Self {
            namespace: self.namespace.clone(),
            component: component.into(),
        }
    }

    #[must_use]
    pub fn as_dotted(&self) -> String {
        if self.namespace.is_empty() {
            return self.component.clone();
        }
        let mut parts = self.namespace.clone();
        parts.push(self.component.clone());
        parts.join(".")
    }
}

impl fmt::Display for OtName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.as_dotted())
    }
}
