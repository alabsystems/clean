// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::{parser::Parser, SourceError};
use crate::expr::{Expr, Stmt};
use crate::types::RustType;

impl Parser {
    pub(crate) fn parse_block(&mut self, block: &syn::Block) -> Result<Expr, SourceError> {
        let snapshot = self.snapshot_item_registries();
        self.collect_block_items(&block.stmts)?;
        let parsed = (|| {
            let mut stmts = Vec::new();
            let mut expr = None;
            let last_idx = block.stmts.len().saturating_sub(1);
            for (idx, stmt) in block.stmts.iter().enumerate() {
                match stmt {
                    syn::Stmt::Local(local) => stmts.push(self.parse_local(local)?),
                    syn::Stmt::Item(item) => {
                        // `type` aliases are resolved structurally via the alias
                        // table (collected above) but are still emitted as items
                        // so the block AST records them. Other purely
                        // declarative items (`use`, `mod`, macros, ...) are
                        // skipped: they have no runtime representation here.
                        if !matches!(
                            item,
                            syn::Item::Use(_)
                                | syn::Item::Macro(_)
                                | syn::Item::ExternCrate(_)
                                | syn::Item::Mod(_)
                                | syn::Item::ForeignMod(_)
                                | syn::Item::TraitAlias(_)
                        ) {
                            let parsed_item = self.with_isolated_type_params(|parser| {
                                parser.parse_item(item.clone())
                            })?;
                            stmts.push(Stmt::Item(parsed_item));
                        }
                    }
                    syn::Stmt::Expr(stmt_expr, semi) => {
                        let parsed = self.parse_expr(stmt_expr)?;
                        if idx == last_idx && semi.is_none() {
                            expr = Some(Box::new(parsed));
                        } else {
                            stmts.push(Stmt::Expr(parsed));
                        }
                    }
                    syn::Stmt::Macro(stmt_mac) => {
                        if Self::builtin_macro_dispatch_name(&stmt_mac.mac.path).is_none() {
                            // Unrecognized macros in statement position are
                            // silently skipped, matching the Item::Macro filter.
                            continue;
                        }
                        let parsed = self.parse_macro_invocation(&stmt_mac.mac)?;
                        if idx == last_idx && stmt_mac.semi_token.is_none() {
                            expr = Some(Box::new(parsed));
                        } else {
                            stmts.push(Stmt::Expr(parsed));
                        }
                    }
                }
            }
            Ok(Expr::Block { stmts, expr })
        })();
        self.restore_item_registries(snapshot);
        parsed
    }

    fn parse_local(&mut self, local: &syn::Local) -> Result<Stmt, SourceError> {
        let (pat, ty) = self.unpack_typed_pat(&local.pat)?;
        let init = local
            .init
            .as_ref()
            .map(|init| self.parse_expr(&init.expr).map(Box::new))
            .transpose()?;
        let else_block = local
            .init
            .as_ref()
            .and_then(|init| init.diverge.as_ref().map(|(_, expr)| expr))
            .map(|expr| self.parse_expr(expr).map(Box::new))
            .transpose()?;
        Ok(Stmt::Let {
            pattern: self.parse_pattern(pat)?,
            ty,
            init,
            else_block,
        })
    }

    fn unpack_typed_pat<'a>(
        &mut self,
        pat: &'a syn::Pat,
    ) -> Result<(&'a syn::Pat, Option<RustType>), SourceError> {
        match pat {
            syn::Pat::Type(pat_type) => Ok((&pat_type.pat, Some(self.parse_type(&pat_type.ty)?))),
            other => Ok((other, None)),
        }
    }
}
