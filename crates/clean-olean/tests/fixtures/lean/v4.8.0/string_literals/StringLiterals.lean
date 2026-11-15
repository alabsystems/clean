-- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
import Init.Data.String.Basic

namespace StringLiterals

theorem empty : ("" : String) = String.mk [] := rfl
theorem ascii : ("enum" : String) = String.mk ['e', 'n', 'u', 'm'] := rfl
theorem unicode : ("😀é" : String) = String.mk ['😀', 'é'] := rfl
theorem unequal_ascii : ("enum" : String) ≠ "struct" := by decide
theorem unequal_unicode : ("😀é" : String) ≠ "😀z" := by decide
theorem unequal_empty : ("" : String) ≠ "a" := by decide

end StringLiterals
