-- Copyright 2026 Project Maintainers
-- Author: Project Maintainer <maintainer@example.invalid>
-- SPDX-License-Identifier: Apache-2.0

-- Public demo fixture: clean accepts this small kernel-check workload without
-- trust debt.

def demoId (A : Type) (x : A) := x

def demoCompose (A : Type) (B : Type) (C : Type)
    (f : B -> C) (g : A -> B) (x : A) := f (g x)

theorem demoImpId (P : Prop) : P -> P := fun h => h

def main : Nat := 0
