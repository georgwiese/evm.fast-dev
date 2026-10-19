import InitECandidate.Solver.GasBudget.CallFirstFeeSites
import InitECandidate.Solver.GasBudget.WarmAddressExceptionPrefix
import InitECandidate.Solver.GasBudget.CallFeeExceptionSetup
import InitECandidate.Solver.GasBudget.CallValueFeeException

namespace InitECandidate.Solver.GasBudget.CallFirstFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query memoryCost expand gas used : BitVec 64)
    (words : U256Zero.Quad) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source .account plan slots cursor floor) (environment : WarmKeys.Environment source)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (vz : source.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word query)])
    (run : evaluateHOLFiniteState source (program arguments continuation) = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧
      ∃ paid, paid ≤ 8 * slots.length + 6 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ warm paid ready inner, paid ≤ 8 * slots.length + 6 ∧ ChargeEvent source ready frame paid (amount warm memoryCost words).toNat ∧
      memoryCost.toNat + (CallGas.stipend words).toNat + 100 ≤ (amount warm memoryCost words).toNat ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  obtain ⟨warmPaid, warm, warmPost, positive, warmBound, warmFits, binary, warmRun, warmScope⟩ :=
    WarmAddress.exception_prefix source post frame query plan slots cursor floor table environment installed ev tableMapped tableCell queryFits queryMapped
      "warm" arguments (CallAccessFee.program (CallValueFee.withTransfer continuation)) args identifier payload run
  let warmed := bind {source with clock := source.clock - warmPaid} "warm" warm
  obtain ⟨accessReady, accessPost, accessFields, accessCell, accessOther, accessRun, accessScope⟩ :=
    CallAccessFee.setup_exception warmed warmPost warm (CallValueFee.withTransfer continuation) identifier payload (bind_lookup_same _ _ _) warmRun
  have warmOther (key : String) (other : ofString "warm" ≠ ofString key) : warmed.locals.lookup (ofString key) = source.locals.lookup (ofString key) := bind_lookup_other _ _ _ _ other
  have accessVZ := (accessOther "vz" (by decide)).trans ((warmOther "vz" (by decide)).trans vz)
  have accessX := (accessOther "x" (by decide)).trans ((warmOther "x" (by decide)).trans xCell)
  obtain ⟨feeSource, feePost, transferFields, feeAccess, transferCell, feeX, feeRun, transferScope⟩ :=
    CallValueFee.setup_exception accessReady accessPost (CallAccessFee.resultWord warm) memoryCost expand words continuation identifier payload accessVZ accessCell accessX accessRun
  have before : emptyLocalsHOLFinite feeSource = emptyLocalsHOLFinite {source with clock := source.clock - warmPaid} := transferFields.trans accessFields
  have beforeMemory := congrArg PanSemStateFiniteExact.memory before
  have beforeGlobals := congrArg PanSemStateFiniteExact.globals before
  have beforeCode := congrArg PanSemStateFiniteExact.code before
  have beforeDomain := congrArg PanSemStateFiniteExact.memaddrs before
  have beforeShapes := congrArg PanSemStateFiniteExact.eshapes before
  change feeSource.memory = source.memory at beforeMemory
  change feeSource.globals = source.globals at beforeGlobals
  change feeSource.code = source.code at beforeCode
  change feeSource.memaddrs = source.memaddrs at beforeDomain
  change feeSource.eshapes = source.eshapes at beforeShapes
  have beforeClock := congrArg PanSemStateFiniteExact.clock before
  change feeSource.clock = source.clock - warmPaid at beforeClock
  have effect := StackPop.PrefixEffect.unchanged source feeSource frame warmPaid warmFits beforeClock before
  have currentOriginal : Input.OriginalCode.Installed feeSource.code := by rw [beforeCode]; exact installed
  have currentEv : feeSource.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [beforeGlobals]; exact ev
  have currentCap : regularBudget feeSource.memory frame ≤ 16777216 := by rw [beforeMemory]; exact cap
  have addCode : feeSource.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one) := by
    have code := OriginalCodeEnvironment.arithmetic feeSource.code currentOriginal .add_sat
    rw [ChargeWithMemory.add_signature] at code
    exact code
  rcases CallValueFee.exception_prefix feeSource feePost frame (CallAccessFee.resultWord warm) memoryCost expand gas used words continuation identifier payload
      currentEv feeAccess transferCell feeX (CallAccessFee.range warm).1 (CallAccessFee.range warm).2 addCode
      (OriginalCodeEnvironment.charge_gas feeSource.code currentOriginal)
      (by rw [beforeDomain]; exact gasMapped) (by rw [beforeDomain]; exact usedMapped)
      (by rw [beforeMemory]; exact gasCell) (by rw [beforeMemory]; exact usedCell) currentCap (by rw [beforeShapes]; exact shape) feeRun with failed | charged
  · obtain ⟨actualId, actualPayload, failedEffect⟩ := failed
    have scopes : emptyLocalsHOLFinite post = emptyLocalsHOLFinite feePost := by rw [warmScope, accessScope, transferScope]; rfl
    apply Or.inl
    refine ⟨actualId, actualPayload, warmPaid + 2, ?_, (effect.trans failedEffect).of_emptyLocals scopes⟩
    have price := price_exact slots.length
    omega
  · obtain ⟨ready, inner, event, surplus, tailRun, feeScope⟩ := charged
    refine Or.inr ⟨warm, warmPaid + 2, ready, inner, ?_, event.prepend effect, surplus, tailRun, ?_, ?_⟩
    · have price := price_exact slots.length
      omega
    · rw [warmScope, accessScope, transferScope, feeScope]; rfl
    · rw [warmScope, accessScope, transferScope, feeScope]; rfl

end InitECandidate.Solver.GasBudget.CallFirstFee

#print axioms InitECandidate.Solver.GasBudget.CallFirstFee.exception_prefix
