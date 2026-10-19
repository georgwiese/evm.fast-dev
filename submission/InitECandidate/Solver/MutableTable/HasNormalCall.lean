import InitECandidate.Solver.MutableTable.HasNormalBody
import InitECandidate.Solver.MutableTable.HasEnvironment
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.MutableTable.PureValueCall

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original membership declaration resumes with its binary answer, preserving every nonlocal field except the paid clock.
The enclosing normal execution derives funding and the real callee result. -/
theorem model_normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hasCode : source.code.lookup (ofString "htab_has") = some (formals, body, .one))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_has") arguments continuation) = (some (.returned returned), post)) :
    ∃ paid flag finish, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word flag)) {source with clock := source.clock - paid}) continuation = (some (.returned returned), finish) ∧
      post = restore source name finish := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "htab_has") arguments continuation returned normal
  obtain ⟨callee, called, tableLocal, keyLocal⟩ := Has.environment source.code.lookup (cell plan .header 0) query hasCode
  obtain ⟨target, actualReturned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "htab_has") arguments _ body continuation callee .one args called positive returned normal
  let entry := callEntryStateHOLFinite source callee
  have entryTable : TableState entry kind plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  obtain ⟨paid, flag, bounded, fits, binary, resultEq, frame⟩ := model_body_normal entry target kind plan slots cursor floor entryTable
    (environment.of_fields rfl rfl rfl) query queryFits queryMapped tableLocal keyLocal actualReturned bodyRun
  rw [resultEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word flag))) .one && shapeEqHOL (shapeOfHOLExact (.val (.word flag))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL_eq_true]
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := pure_value_call source target name (ofString "htab_has") .one .one arguments _ body continuation callee
    (.val (.word flag)) paid args called positive bodyRun shapePass callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  rw [subtract] at actual
  rw [actual] at normal
  let ready := setVarHOLFinite (ofString name) (.val (.word flag)) {source with clock := source.clock - (paid + 1)}
  let finish := (evaluateHOLFiniteState ready continuation).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready continuation).1 = some (.returned returned) at result
  have frameEq := congrArg Prod.snd normal
  change paid ≤ source.clock - 1 at fits
  exact ⟨paid + 1, flag, finish, by omega, by omega, by omega, binary, Prod.ext result rfl, frameEq.symm⟩

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.model_normal_entry
