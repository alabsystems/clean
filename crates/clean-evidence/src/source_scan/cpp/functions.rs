// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function definitions in the pinned C++ inventory's masked source.

use std::{collections::BTreeMap, ops::Range};

use super::arms::{case_arms, CppCaseArm};
use super::constants::{constant_uses, CppConstantUse};
use super::headers::{classify, skip_access, Header};
use super::{python_whitespace, CppSource};

/// A definition identified by the pinned C++ inventory scanner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CppFunction {
    /// Class-qualified name with a one-based `#` suffix for file-local overloads.
    pub name: String,
    /// One-based inclusive LF line span in the masked source.
    pub lines: [usize; 2],
    /// Half-open byte range in the mask, from the header through the closing brace.
    pub masked_bytes: Range<usize>,
    /// Case label runs in the incumbent's switch discovery order.
    pub case_arms: Vec<CppCaseArm>,
    /// One-based masked LF lines in the inclusive span that contain code.
    pub code_lines: Vec<usize>,
    /// Hardcoded constant occurrences sorted by masked line and name.
    pub hardcoded_constants: Vec<CppConstantUse>,
}

/// A refusal from the C++ inventory's definition walk.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CppFunctionError {
    #[error("braces or parentheses do not balance after blanking")]
    Unbalanced,
    #[error("stray closing brace at line {line}")]
    StrayClose { line: usize },
    #[error("cannot name the definition at line {line}")]
    Unnamed { line: usize },
    #[error("switch without a body at line {line}")]
    SwitchWithoutBody { line: usize },
    #[error("unbalanced braces")]
    UnbalancedBraces,
}

enum Scope<'a> {
    Namespace,
    Class(&'a str),
    Function { name: String, start: usize },
    Block,
}

impl CppSource<'_> {
    /// Extract the incumbent scanner's function definitions in source order.
    ///
    /// # Errors
    ///
    /// Reports malformed definitions or switch bodies using the same masked
    /// coordinates as the incumbent scanner.
    pub fn functions(&self) -> Result<Vec<CppFunction>, CppFunctionError> {
        self.functions_with_constant_names(&self.global_constant_names(), &BTreeMap::new())
    }

    /// Extract functions with precomputed local and shared global names.
    ///
    /// The local table takes precedence over the shared table.
    ///
    /// # Errors
    ///
    /// Reports malformed definitions or switch bodies in masked coordinates.
    pub fn functions_with_constant_names(
        &self,
        local: &BTreeMap<String, String>,
        shared: &BTreeMap<String, String>,
    ) -> Result<Vec<CppFunction>, CppFunctionError> {
        let code = self.masked();
        let line_starts = balanced_line_starts(code)?;
        let mut functions = Vec::new();
        let mut scopes = Vec::new();
        let mut statement_start = 0;
        let mut parens = 0_isize;

        for (at, byte) in code.bytes().enumerate() {
            match byte {
                b'(' => parens += 1,
                b')' => parens -= 1,
                b'{' => {
                    let scope = if parens > 0 || !at_declaration_scope(&scopes) {
                        Scope::Block
                    } else {
                        let header = &code[skip_access(code, statement_start)..at];
                        match classify(header) {
                            Header::Namespace => Scope::Namespace,
                            Header::Class(name) => Scope::Class(name),
                            Header::Block => Scope::Block,
                            Header::Function(name) => Scope::Function {
                                name: qualify_name(&scopes, name),
                                start: at - header.trim_start_matches(python_whitespace).len(),
                            },
                            Header::Unnamed => {
                                return Err(CppFunctionError::Unnamed {
                                    line: line_of(&line_starts, at),
                                });
                            }
                        }
                    };
                    // The statement cursor carries into a new scope until a
                    // declaration-level semicolon or a closing brace resets it.
                    scopes.push(scope);
                }
                b'}' => {
                    let scope = scopes.pop().ok_or_else(|| CppFunctionError::StrayClose {
                        line: line_of(&line_starts, at),
                    })?;
                    if let Scope::Function { name, start } = scope {
                        functions.push(CppFunction {
                            name,
                            lines: [line_of(&line_starts, start), line_of(&line_starts, at)],
                            masked_bytes: start..at + 1,
                            case_arms: Vec::new(),
                            code_lines: Vec::new(),
                            hardcoded_constants: Vec::new(),
                        });
                    }
                    if at_declaration_scope(&scopes) {
                        statement_start = at + 1;
                    }
                }
                b';' if parens == 0 && at_declaration_scope(&scopes) => {
                    statement_start = at + 1;
                }
                _ => {}
            }
        }

        number_overloads(&mut functions);
        for function in &mut functions {
            function.case_arms = case_arms(code, &line_starts, function.masked_bytes.clone())?;
            function.code_lines = nonblank_lines(code, &line_starts, function.lines);
            let base = function
                .name
                .rsplit_once("::")
                .map_or(function.name.as_str(), |(_, base)| base);
            if !base.starts_with("initialize_") && !base.starts_with("finalize_") {
                function.hardcoded_constants = constant_uses(
                    self,
                    &line_starts,
                    function.masked_bytes.clone(),
                    local,
                    shared,
                );
            }
        }
        Ok(functions)
    }
}

fn balanced_line_starts(code: &str) -> Result<Vec<usize>, CppFunctionError> {
    let mut starts = vec![0];
    let (mut braces, mut parens) = (0_isize, 0_isize);
    for (at, byte) in code.bytes().enumerate() {
        match byte {
            b'{' => braces += 1,
            b'}' => braces -= 1,
            b'(' => parens += 1,
            b')' => parens -= 1,
            b'\n' => starts.push(at + 1),
            _ => {}
        }
    }
    // Aggregate imbalance takes precedence over errors located during the walk.
    if braces != 0 || parens != 0 {
        return Err(CppFunctionError::Unbalanced);
    }
    Ok(starts)
}

pub(super) fn line_of(starts: &[usize], at: usize) -> usize {
    starts.partition_point(|&start| start <= at)
}

fn nonblank_lines(code: &str, starts: &[usize], [first, last]: [usize; 2]) -> Vec<usize> {
    (first..=last)
        .filter(|&line| {
            let start = starts[line - 1];
            let end = starts.get(line).copied().unwrap_or(code.len());
            !code[start..end].chars().all(python_whitespace)
        })
        .collect()
}

fn at_declaration_scope(scopes: &[Scope<'_>]) -> bool {
    matches!(
        scopes.last(),
        None | Some(Scope::Namespace | Scope::Class(_))
    )
}

fn qualify_name(scopes: &[Scope<'_>], name: String) -> String {
    let mut qualified = String::new();
    for scope in scopes {
        if let Scope::Class(class) = scope {
            qualified.push_str(class);
            qualified.push_str("::");
        }
    }
    if qualified.is_empty() {
        name
    } else {
        qualified.push_str(&name);
        qualified
    }
}

fn number_overloads(functions: &mut [CppFunction]) {
    // The walk cannot nest function definitions, so closing order is source
    // order. The stable name sort keeps that order within each overload set.
    functions.sort_by(|left, right| left.name.cmp(&right.name));
    for overloads in functions.chunk_by_mut(|left, right| left.name == right.name) {
        if overloads.len() > 1 {
            for (index, function) in overloads.iter_mut().enumerate() {
                function.name = format!("{}#{}", function.name, index + 1);
            }
        }
    }
    functions.sort_by_key(|function| function.masked_bytes.start);
}

#[cfg(test)]
mod tests {
    use super::{CppFunctionError, CppSource};

    #[test]
    fn extracts_class_overloads_and_extern_in_source_order() {
        let source = CppSource::new(concat!(
            "#define HIDDEN \\\n",
            "  int fake() { return 0; }\n",
            "namespace Demo {\n",
            "int cursor_reset;\n",
            "struct Worker {\n",
            "int field;\n",
            "private: public:\n",
            "int run(int value) {\n",
            "    auto closure = [](int x) { return x; };\n",
            "    return closure(value);\n",
            "}\n",
            "int run(bool value) { return value; }\n",
            "};\n",
            "}\n",
            "extern \"C\" {\n",
            "int cursor_reset;\n",
            "int Ffi() { return 0; }\n",
            "}\n",
        ));
        let functions = source.functions().expect("valid fixture");
        let spans: Vec<_> = functions
            .iter()
            .map(|function| (function.name.as_str(), function.lines))
            .collect();
        assert_eq!(
            spans,
            [
                ("Worker::run#1", [8, 11]),
                ("Worker::run#2", [12, 12]),
                ("Ffi", [17, 17]),
            ]
        );
        assert_eq!(
            source.raw_slice(functions[1].masked_bytes.clone()),
            Some("int run(bool value) { return value; }")
        );
    }

    #[test]
    fn uses_masked_lf_positions_and_retains_original_function_bytes() {
        let source = CppSource::new("/* \u{2028}α */\r\n\u{2003}int f() { /*β*/ return 0; }\r\n");
        let functions = source.functions().expect("valid fixture");
        let [function] = functions.as_slice() else {
            panic!("expected one function, got {functions:?}");
        };
        assert_eq!(function.name, "f");
        assert_eq!(function.lines, [2, 2]);
        assert_eq!(source.raw_lines(2, 2), Some("α */\r\n"));
        assert_eq!(
            source.raw_slice(function.masked_bytes.clone()),
            Some("int f() { /*β*/ return 0; }")
        );
    }

    #[test]
    fn preserves_aggregate_balance_and_cursor_refusals() {
        let unframed = concat!(
            "namespace Demo {\n",
            "struct Worker {\n",
            "public:\n",
            "int run(int shape) {\n",
            "int frame;\n",
            "switch (shape) { default: return shape; }\n",
            "}\n",
            "};\n",
            "}\n",
        );
        for (input, expected) in [
            ("}\n", CppFunctionError::Unbalanced),
            ("int f() { return 0;", CppFunctionError::Unbalanced),
            ("int f() { g(; }", CppFunctionError::Unbalanced),
            ("\n}{\n", CppFunctionError::StrayClose { line: 2 }),
            (
                "if (true) { return 0; }",
                CppFunctionError::Unnamed { line: 1 },
            ),
            (unframed, CppFunctionError::Unnamed { line: 6 }),
        ] {
            assert_eq!(
                CppSource::new(input).functions(),
                Err(expected),
                "{input:?}"
            );
        }

        let source = CppSource::new(") ;\nint f() { return 1; }\n(\n");
        let functions = source.functions().expect("aggregate balance succeeds");
        assert_eq!(functions[0].lines, [1, 2]);
    }
}
