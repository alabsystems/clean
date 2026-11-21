/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
prelude
import Init.Prelude

inductive TwoHeads where
  | single (children : List TwoHeads)
  | nested (slots : List (Option TwoHeads))

inductive SameHead where
  | nested (children : List (List SameHead))
