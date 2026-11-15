// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cross-crate policy access used by Trust's stand-in import census.

use clean_elab::FileContext;

#[test]
fn trust_consumer_can_read_external_import_policy_without_changing_it() {
    let mut context = FileContext::new();
    assert!(context.external_import_search_enabled());
    assert!(context.external_import_search_enabled());

    context.disable_external_import_search();
    assert!(!context.external_import_search_enabled());
    assert!(!context.clone().external_import_search_enabled());
    assert!(FileContext::new().external_import_search_enabled());
}
