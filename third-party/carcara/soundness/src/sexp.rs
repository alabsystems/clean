// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A lossless-enough S-expression reader/printer for SMT-LIB and Alethe text.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

impl Sx {
    pub fn atom(s: &str) -> Sx {
        Sx::Atom(s.to_owned())
    }

    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Sx::Atom(a) => Some(a),
            Sx::List(_) => None,
        }
    }

    pub fn head(&self) -> Option<&str> {
        match self {
            Sx::List(items) => items.first().and_then(Sx::as_atom),
            Sx::Atom(_) => None,
        }
    }

    pub fn print(&self, out: &mut String) {
        match self {
            Sx::Atom(a) => out.push_str(a),
            Sx::List(items) => {
                out.push('(');
                for (i, it) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    it.print(out);
                }
                out.push(')');
            }
        }
    }

    pub fn to_text(&self) -> String {
        let mut s = String::new();
        self.print(&mut s);
        s
    }
}

pub fn print_all(items: &[Sx]) -> String {
    let mut s = String::new();
    for it in items {
        it.print(&mut s);
        s.push('\n');
    }
    s
}

/// Parse a sequence of S-expressions. Returns `None` on unbalanced input.
pub fn parse(text: &str) -> Option<Vec<Sx>> {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut stack: Vec<Vec<Sx>> = vec![Vec::new()];
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == ';' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '(' {
            stack.push(Vec::new());
            i += 1;
        } else if c == ')' {
            let done = stack.pop()?;
            stack.last_mut()?.push(Sx::List(done));
            i += 1;
        } else if c == '"' {
            let start = i;
            i += 1;
            loop {
                if i >= chars.len() {
                    return None;
                }
                if chars[i] == '"' {
                    if i + 1 < chars.len() && chars[i + 1] == '"' {
                        i += 2;
                        continue;
                    }
                    i += 1;
                    break;
                }
                i += 1;
            }
            stack
                .last_mut()?
                .push(Sx::Atom(chars[start..i].iter().collect()));
        } else if c == '|' {
            let start = i;
            i += 1;
            while i < chars.len() && chars[i] != '|' {
                i += 1;
            }
            if i >= chars.len() {
                return None;
            }
            i += 1;
            stack
                .last_mut()?
                .push(Sx::Atom(chars[start..i].iter().collect()));
        } else {
            let start = i;
            while i < chars.len()
                && !chars[i].is_whitespace()
                && !matches!(chars[i], '(' | ')' | '"' | ';' | '|')
            {
                i += 1;
            }
            stack
                .last_mut()?
                .push(Sx::Atom(chars[start..i].iter().collect()));
        }
    }
    if stack.len() == 1 {
        stack.pop()
    } else {
        None
    }
}
