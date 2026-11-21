-- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
prelude
import Roundtrip

noncomputable def useRecOn (chain : ExportChain) : ExportChain :=
  ExportChain.recOn (motive := fun _ => ExportChain) chain
    ExportChain.stop (fun _ copied => ExportChain.link copied)
