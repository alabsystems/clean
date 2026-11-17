/- The complete original-text codec must remain independent of any program
   semantics. These refusals fail if a future codec import reintroduces SemR.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRBooleanClaimText

open SemRBooleanClaim

/-- error: Unknown identifier `SemR.Module` -/
#guard_msgs in
#check SemR.Module

/-- error: Unknown identifier `SemR.runFunction` -/
#guard_msgs in
#check SemR.runFunction

/-- error: Unknown identifier `SemRBooleanWP.constWP` -/
#guard_msgs in
#check SemRBooleanWP.constWP

-- The original typed text uses the same integer interpreter and refuses an
-- unbound identifier even when its branch cannot determine the Boolean result.
example : checkedTypedText 4096 [100,32,33,61,32,48] [] [[100]]
    ([], [([100], 1)]) = some true := by decide
example : checkedTypedText 4096 [100,32,33,61,32,48] [] [[100]]
    ([], [([100], 0)]) = some false := by decide
example : checkedTypedText 4096 [100,32,33,61,32,48] [] []
    ([], [([100], 1)]) = none := by decide
example : checkedTypedText 4096
    [102,97,108,115,101,32,38,38,32,117,110,107,110,111,119,110] [] []
    ([], []) = none := by decide
