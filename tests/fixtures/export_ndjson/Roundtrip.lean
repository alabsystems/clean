-- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
prelude
import ExportSupport

inductive ExportChain where
  | stop
  | link (tail : ExportChain)

-- Primitive recursion. Each link receives the result for its tail.
noncomputable def exportCopy (chain : ExportChain) : ExportChain :=
  ExportChain.rec (motive := fun _ => ExportChain)
    ExportChain.stop (fun _ copied => ExportChain.link copied) chain

theorem exportFirst (p : ExportChain → Prop) (h : p ExportChain.stop) :
    exportMeaning (p (exportCopy ExportChain.stop)) := h

theorem exportSecond (p : ExportChain → Prop) (h : p (ExportChain.link ExportChain.stop)) :
    exportMeaning (p (exportCopy (ExportChain.link ExportChain.stop))) := h
