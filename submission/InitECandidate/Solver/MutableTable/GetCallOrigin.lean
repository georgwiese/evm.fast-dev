import InitECandidate.Solver.MutableTable.GetNormalOrigin
import InitECandidate.Solver.MutableTable.GetCall32
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original getter declaration resumes with its binary flag and
actual stored word, preserving every nonlocal field except the paid clock.
The enclosing normal execution derives funding and the real callee result. -/
theorem model_normal_entry_origin (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") arguments continuation) = (some (.returned returned), post)) :
    ∃ paid flag value finish, 1 ≤ paid ∧ paid ≤ (Find.generalProbePrice kind * slots.length + (KeyHash.hashPrice kind + 1)) + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧ ValueOrigin source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) flag value (fun slot=>slot.toNat∈slots) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - paid}) continuation = (some (.returned returned), finish) ∧
      post = restore source name finish := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) pairShape (ofString "htab_get") arguments continuation returned normal
  obtain ⟨callee, called, tableLocal, keyLocal⟩ := Get.environment source.code.lookup (cell plan .header 0) query getCode
  obtain ⟨target, actualReturned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) pairShape (ofString "htab_get") arguments _ body continuation callee pairShape args called positive returned normal
  let entry := callEntryStateHOLFinite source callee
  have entryTable : TableState entry kind plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  obtain ⟨paid, flag, value, bounded, fits, binary, origin, resultEq, frame⟩ := model_body_normal_origin entry target kind plan slots cursor floor entryTable
    (environment.of_fields rfl rfl rfl) query queryFits queryMapped tableLocal keyLocal actualReturned bodyRun
  rw [resultEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (pair flag value)) pairShape && shapeEqHOL (shapeOfHOLExact (pair flag value)) pairShape) = true := by
    simp [pair, pairShape, shapeOfHOLExact, shapeEqHOL_eq_true]
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := pure_value_call source target name (ofString "htab_get") pairShape pairShape arguments _ body continuation callee
    (pair flag value) paid args called positive bodyRun shapePass callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  rw [subtract] at actual
  rw [actual] at normal
  let ready := setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - (paid + 1)}
  let finish := (evaluateHOLFiniteState ready continuation).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready continuation).1 = some (.returned returned) at result
  have frameEq := congrArg Prod.snd normal
  change paid ≤ source.clock - 1 at fits
  exact ⟨paid + 1, flag, value, finish, by omega, by omega, by omega, binary, origin, Prod.ext result rfl, frameEq.symm⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_normal_entry_origin
