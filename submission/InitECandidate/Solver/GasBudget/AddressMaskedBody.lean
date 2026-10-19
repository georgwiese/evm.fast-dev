import InitECandidate.Solver.GasBudget.AddressMaskedStores
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "to_address_masked") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 402 (OriginalCodeEnvironment.originalEntry Guest.guestFn_to_address_masked) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals, U256Value.tupleShape,
    Guest.guestFn_to_address_masked, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (valueLocal : source.locals.lookup (ofString "v") = some (U256Value.tuple words))
    (mapped : BytesMapped source (frame + 240#64) 20)
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word (frame + 240#64)) ∧ ∃ paid, paid ≤ 7 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway (frame + 240#64) query 20 → post.memory query = source.memory query) := by
  have pointerRead : eval source pointerExpression = some (.val (.word (frame + 240#64))) := by
    simp [eval, pointerExpression, evalHOLExact, evalListHOLExact, toExact, ev, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [body_shape] at run
  obtain ⟨inner, storesRun, scope⟩ := Input.declaration_return_word source post "a" pointerExpression (frame + 240#64) stores returned pointerRead run
  let entered := bind source "a" (frame + 240#64)
  have value : entered.locals.lookup (ofString "v") = some (U256Value.tuple words) := (bind_lookup_other _ _ _ _ (by decide)).trans valueLocal
  obtain ⟨valueEq, paid, bounded, funded, clock, fields, away⟩ := stores_normal entered inner (frame + 240#64) words installed (bind_lookup_same _ _ _) value mapped returned storesRun
  refine ⟨valueEq, paid, bounded, funded, ?_, ?_, ?_⟩
  · rw [scope]; exact clock
  · rw [scope]; exact fields
  · intro query outside
    rw [scope]
    exact away query outside

end InitECandidate.Solver.GasBudget.AddressMasked

#print axioms InitECandidate.Solver.GasBudget.AddressMasked.original_code
#print axioms InitECandidate.Solver.GasBudget.AddressMasked.body_normal
