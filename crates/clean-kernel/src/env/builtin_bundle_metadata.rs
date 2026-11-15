// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source binder identities live in environment metadata, not kernel Expr.
//! Install them only after the whole selected cluster passes checked admission.

use super::{
    array, binder, boolean, field, name, number, part, text, BinderInfo, Environment, Name, Result,
};
use serde_json::Value;

#[derive(Clone)]
pub(super) struct HeaderMetadata {
    params: Vec<(Name, BinderInfo)>,
    value_foralls: Option<(usize, Vec<Name>)>,
    noncomputable: bool,
    irreducible: bool,
}

fn node(nodes: &[Value], id: u32) -> Result<&[Value]> {
    array(
        nodes
            .get(id as usize)
            .ok_or("invalid header expression reference")?,
    )
}

pub(super) fn read(raw: &Value, nodes: &[Value]) -> Result<HeaderMetadata> {
    let mut at = number(field(raw, "type")?)?;
    let mut params = Vec::new();
    loop {
        let value = node(nodes, at)?;
        match text(part(value, 0)?)? {
            "pi" => {
                params.push((name(part(value, 1)?, 0)?, binder(part(value, 2)?)?));
                at = number(part(value, 4)?)?;
            }
            "mdata" => at = number(part(value, 2)?)?,
            _ => break,
        }
    }
    let mut value_foralls = None;
    if let Some(value) = raw.get("value") {
        let mut at = number(value)?;
        let mut lambdas = 0;
        let mut names = Vec::new();
        loop {
            let value = node(nodes, at)?;
            match text(part(value, 0)?)? {
                "lam" if names.is_empty() => {
                    lambdas += 1;
                    at = number(part(value, 4)?)?;
                }
                "pi" => {
                    names.push(name(part(value, 1)?, 0)?);
                    at = number(part(value, 4)?)?;
                }
                "mdata" => at = number(part(value, 2)?)?,
                _ => break,
            }
        }
        if !names.is_empty() {
            value_foralls = Some((lambdas, names));
        }
    }
    Ok(HeaderMetadata {
        params,
        value_foralls,
        noncomputable: boolean(field(raw, "noncomputable")?)
            .map_err(|e| format!("invalid noncomputable metadata: {e}"))?,
        irreducible: text(field(raw, "kind")?)? == "definition"
            && text(field(raw, "source_reducibility")?)? == "[irreducible]",
    })
}

impl HeaderMetadata {
    pub(super) fn is_noncomputable(&self) -> bool {
        self.noncomputable
    }

    pub(super) fn is_irreducible(&self) -> bool {
        self.irreducible
    }

    pub(super) fn install(
        &self,
        env: &mut Environment,
        name: &Name,
        is_definition: bool,
    ) -> Result<()> {
        env.add_checked_param_infos(name, self.params.clone(), true)
            .map_err(|e| e.to_string())?;
        if is_definition && self.irreducible {
            env.restrict_checked_unfolding(name)
                .map_err(|e| e.to_string())?;
        }
        if self.noncomputable {
            env.mark_noncomputable(name.clone());
        } else {
            // A checked upgrade can replace a placeholder with stale tags.
            env.noncomputable_decls.remove(name);
        }
        if is_definition {
            if let Some((lambdas, names)) = &self.value_foralls {
                env.record_value_forall_binder_names(name.clone(), *lambdas, names.clone());
            } else if env.get_value_forall_binder_names(name).is_some() {
                env.value_binder_table_mut().remove(name);
            }
        }
        Ok(())
    }
}
