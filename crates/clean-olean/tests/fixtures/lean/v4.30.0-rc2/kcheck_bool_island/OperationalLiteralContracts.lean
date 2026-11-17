prelude
import KCheckBoolIsland.CompleteOperationalRun
set_option autoImplicit false
namespace BoolOperationalLiteralContracts
open KCheck KCheckSpec KCheckBoolIsland
open KCheckBoolIsland.OperationalCases KCheckBoolIsland.RecursorOperational KCheckBoolIsland.SlotOperational

def recursor_checked : Prop := checkOrdinary E8 recursorOrdinary recursorAdvice = .ok recursorEntry

def recursor_accepted : Prop := kcheck E8 (.ordinary recursorHeader.ordinary) recursorAdvice = .ok (E9, Receipt.of recursorEntry)

def zeroSlot_checked : Prop := checkOrdinary E9 (slotOrdinary false) (slotAdvice false) = .ok zeroSlotEntry

def oneSlot_checked : Prop := checkOrdinary E10 (slotOrdinary true) (slotAdvice true) = .ok oneSlotEntry

def zeroSlot_accepted : Prop := kcheck E9 (.ordinary zeroSlotHeader.ordinary) (slotAdvice false) = .ok (E10, Receipt.of zeroSlotEntry)

def oneSlot_accepted : Prop := kcheck E10 (.ordinary oneSlotHeader.ordinary) (slotAdvice true) = .ok (E11, Receipt.of oneSlotEntry)

def frames_split : Prop := splitFrames KCheckBoolIsland.CompleteOperationalRun.advice = .ok [encode zTokens, encode kTokens, encode bitTokens, encode formerTokens, encode zeroTokens, encode oneTokens, encode dTokens, encode absurdTokens, encode recursorTokens, encode (slotTokens false), encode (slotTokens true)]

def all_run_accepted : Prop := kcheckRun KCheckBoolIsland.inputs KCheckBoolIsland.CompleteOperationalRun.advice = .ok (E11, [Receipt.of zEntry, Receipt.of kEntry, Receipt.of bitEntry, Receipt.of formerEntry, Receipt.of zeroEntry, Receipt.of oneEntry, Receipt.of dEntry, Receipt.of absurdEntry, Receipt.of recursorEntry, Receipt.of zeroSlotEntry, Receipt.of oneSlotEntry])

end BoolOperationalLiteralContracts
