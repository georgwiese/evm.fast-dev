import InitECandidate.Solver.GasBudget.WarmAddressCall
import InitECandidate.Solver.GasBudget.CallAccessFee
import InitECandidate.Solver.GasBudget.ChargeEvent
import InitECandidate.Solver.GasBudget.ChargeWithMemoryProgram

namespace InitECandidate.Solver.GasBudget.CallFirstFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def program (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "warm") .one (ofString "is_warm_address") arguments
    (CallAccessFee.program (CallValueFee.withTransfer continuation))
def amount (warm memoryCost : BitVec 64) (words : U256Zero.Quad) : BitVec 64 :=
  SaturatingAdd.resultWord (CallAccessFee.resultWord warm + ForwardCredit.valueFee words) memoryCost

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Actual original CALL warmth lookup, access branch, value branch, add_sat
and first charge. The positive event and surplus follow from that execution;
the current table/argument ownership and code premises are explicit. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query memoryCost expand : BitVec 64)
    (words : U256Zero.Quad) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source .account plan slots cursor floor) (environment : WarmKeys.Environment source)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (vz : source.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word query)])
    (run : evaluateHOLFiniteState source (program arguments continuation) = (some (.returned returned), post)) :
    ∃ warm paid ready inner, paid ≤ Has.bodyPrice .account slots.length + 4 ∧
      ChargeEvent source ready frame paid (amount warm memoryCost words).toNat ∧
      memoryCost.toNat + (CallGas.stipend words).toNat + 100 ≤ (amount warm memoryCost words).toNat ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨warmPaid, warm, warmPost, positive, warmBound, warmFits, binary, warmRun, warmScope⟩ :=
    WarmAddress.call_normal source post frame query plan slots cursor floor table environment installed ev tableMapped tableCell queryFits queryMapped
      "warm" arguments (CallAccessFee.program (CallValueFee.withTransfer continuation)) args returned run
  let warmed := bind {source with clock := source.clock - warmPaid} "warm" warm
  obtain ⟨accessReady, accessPost, accessFields, accessCell, accessOther, accessRun, accessScope⟩ :=
    CallAccessFee.setup_normal warmed warmPost warm (CallValueFee.withTransfer continuation) returned (bind_lookup_same _ _ _) warmRun
  have warmOther (key : String) (other : ofString "warm" ≠ ofString key) : warmed.locals.lookup (ofString key) = source.locals.lookup (ofString key) :=
    bind_lookup_other _ _ _ _ other
  have accessVZ := (accessOther "vz" (by decide)).trans ((warmOther "vz" (by decide)).trans vz)
  have accessX := (accessOther "x" (by decide)).trans ((warmOther "x" (by decide)).trans xCell)
  obtain ⟨feeSource, feePost, transferFields, feeAccess, transferCell, feeX, feeRun, transferScope⟩ :=
    CallValueFee.setup_normal accessReady accessPost (CallAccessFee.resultWord warm) memoryCost expand words continuation returned accessVZ accessCell accessX accessRun
  have before : emptyLocalsHOLFinite feeSource = emptyLocalsHOLFinite {source with clock := source.clock - warmPaid} :=
    transferFields.trans accessFields
  have beforeMemory := congrArg PanSemStateFiniteExact.memory before
  have beforeGlobals := congrArg PanSemStateFiniteExact.globals before
  have beforeCode := congrArg PanSemStateFiniteExact.code before
  have beforeClock := congrArg PanSemStateFiniteExact.clock before
  change feeSource.memory = source.memory at beforeMemory
  change feeSource.globals = source.globals at beforeGlobals
  change feeSource.code = source.code at beforeCode
  change feeSource.clock = source.clock - warmPaid at beforeClock
  have currentOriginal : Input.OriginalCode.Installed feeSource.code := by rw [beforeCode]; exact installed
  have currentEv : feeSource.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [beforeGlobals]; exact ev
  have currentCap : regularBudget feeSource.memory frame ≤ 16777216 := by rw [beforeMemory]; exact cap
  have addCode : feeSource.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one) := by
    have code := OriginalCodeEnvironment.arithmetic feeSource.code currentOriginal .add_sat
    rw [ChargeWithMemory.add_signature] at code
    exact code
  obtain ⟨ready, inner, feeFits, feeFields, tailRun, feeScope, budget, credit, surplus, outside⟩ :=
    CallValueFee.normal feeSource feePost frame (CallAccessFee.resultWord warm) memoryCost expand words continuation returned currentEv feeAccess transferCell feeX
      (CallAccessFee.range warm).1 (CallAccessFee.range warm).2 addCode (OriginalCodeEnvironment.charge_gas feeSource.code currentOriginal) currentCap feeRun
  have readyClock := congrArg PanSemStateFiniteExact.clock feeFields
  change ready.clock = feeSource.clock - 2 at readyClock
  have canonical : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {feeSource with memory := ready.memory, clock := ready.clock} := by
    rw [readyClock]
    exact feeFields
  have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) before
  have fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock} := canonical.trans lifted
  have event : ChargeEvent source ready frame (warmPaid + 2) (amount warm memoryCost words).toNat := by
    refine ⟨by omega, by rw [readyClock, beforeClock]; omega, fields, ?_, ?_, by change 0 < (SaturatingAdd.resultWord _ _).toNat; omega, ?_⟩
    · rw [budget, beforeMemory]
    · rw [credit, beforeMemory]
      rfl
    · intro address notSP notGas notUsed
      exact (outside address notGas notUsed).trans (congrFun beforeMemory address)
  refine ⟨warm, warmPaid + 2, ready, inner, by omega, event, surplus, tailRun, ?_⟩
  rw [warmScope, accessScope, transferScope, feeScope]
  rfl

end InitECandidate.Solver.GasBudget.CallFirstFee

#print axioms InitECandidate.Solver.GasBudget.CallFirstFee.normal
