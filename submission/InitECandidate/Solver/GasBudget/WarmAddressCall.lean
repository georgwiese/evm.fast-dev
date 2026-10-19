import InitECandidate.Solver.GasBudget.WarmAddressProgram

namespace InitECandidate.Solver.GasBudget.WarmAddress
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Real is_warm_address scoped caller; collision cost and binary result
come from the actual original membership execution without clock funding. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64))
    (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word query)])
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "is_warm_address") arguments continuation) = (some (.returned returned), post)) :
    ∃ paid answer inner, 1 ≤ paid ∧ paid ≤ Has.bodyPrice .account slots.length + 2 ∧ paid ≤ source.clock ∧
      (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation = (some (.returned returned), inner) ∧
      post = restore source name inner := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "is_warm_address") arguments continuation returned run
  obtain ⟨callee, called, queryLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "is_warm_address") "addr" body query (original_code source.code installed)
  obtain ⟨target, actualReturned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "is_warm_address") arguments _ body continuation callee .one args called positive returned run
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨paid, answer, bounded, funded, binary, resultEq, frameFields⟩ := body_normal entry target frame query plan slots cursor floor
    (table.of_fields rfl rfl rfl rfl) (environment.of_fields rfl rfl rfl) installed ev tableMapped tableCell queryLocal queryFits queryMapped actualReturned bodyRun
  rw [resultEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word answer))) .one && shapeEqHOL (shapeOfHOLExact (.val (.word answer))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL_eq_true]
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frameFields
  have actual := pure_value_call source target name (ofString "is_warm_address") .one .one arguments _ body continuation callee
    (.val (.word answer)) paid args called positive bodyRun shapePass callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  rw [subtract] at actual
  rw [actual] at run
  let ready := bind {source with clock := source.clock - (paid + 1)} name answer
  let inner := (evaluateHOLFiniteState ready continuation).2
  have result := congrArg Prod.fst run
  change (evaluateHOLFiniteState ready continuation).1 = some (.returned returned) at result
  have scope := congrArg Prod.snd run
  change paid ≤ source.clock - 1 at funded
  exact ⟨paid + 1, answer, inner, by omega, by omega, by omega, binary, Prod.ext result rfl, scope.symm⟩

end InitECandidate.Solver.GasBudget.WarmAddress

#print axioms InitECandidate.Solver.GasBudget.WarmAddress.call_normal
