-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0

-- Soundness gate: basic identity and const definitions
-- Source: clean-elab integration tests (basic.rs)
-- Expected: clean and Lean 4 both accept

def gateId (A : Type) (x : A) := x
def gateConst (A : Type) (B : Type) (x : A) (_y : B) := x
