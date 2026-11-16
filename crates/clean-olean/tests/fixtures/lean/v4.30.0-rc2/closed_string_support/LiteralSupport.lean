/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
prelude
import Init.Data.List.Basic
namespace LiteralSupport

def recName : Lean.Name := .str (.str .anonymous "Eq") "rec"
def reflName : Lean.Name := .str (.str .anonymous "Eq") "refl"

theorem different_names : (recName == reflName) = false := rfl
theorem different_strings : ("rec" == "refl") = false := rfl

def entries : List (Lean.Name × Nat) := [(reflName,0),(recName,1)]
theorem lookup_found : entries.filter (fun entry => entry.1 == recName) = [(recName,1)] := rfl
end LiteralSupport
