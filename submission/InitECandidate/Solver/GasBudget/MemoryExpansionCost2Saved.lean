import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Second

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem saved_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame current : BitVec 64) (a : BitVec 64 × BitVec 64) (s2 n2 : U256Value.Words)
    (view : MemoryExpansionCost.View source frame current)
    (savedLocal : source.locals.lookup (ofString "saved") = some (.val (.word current)))
    (aLocal : source.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a))
    (startLocal : source.locals.lookup (ofString "s2") = some (U256Value.tuple s2))
    (sizeLocal : source.locals.lookup (ofString "n2") = some (U256Value.tuple n2))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source afterSaved = (some (.returned returned), post)) :
    returned = MemoryExpansionCost.pairValue (merge a (MemoryExpansionCost.resultPair s2 n2 (current + a.2))) ∧
      ∃ paid : Nat, paid ≤ 21 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        post.memory = source.memory ∧ Input.LocalEffects.erase post = Input.LocalEffects.erase source := by
  have readTemporary : eval source temporaryValue = some (.val (.word (current + a.2))) := by
    simp [eval, temporaryValue, part, evalHOLExact, evalListHOLExact, toExact, localVar, savedLocal, aLocal,
      MemoryExpansionCost.pairValue, valueIsWord, valueWord, wordOpHOL, wordOp]
  have stored := StoreWord.execute source (frameAddress 32#64) temporaryValue (frame + 32#64) (current + a.2)
    (address_read source frame 32#64 view.ev) readTemporary view.mapped
  let temporary := {source with memory := StoreWord.put source.memory (frame + 32#64) (current + a.2)}
  rw [afterSaved, StateSteps.next_sequence source temporary _ afterTemporary stored (Nat.le_refl _)] at run
  have tempView : MemoryExpansionCost.View temporary frame (current + a.2) :=
    ⟨view.installed, view.ev, view.mapped, by simp [temporary, StoreWord.put]⟩
  obtain ⟨value, paid, bound, fits, clock, memory, fields⟩ :=
    second_normal temporary post frame current (current + a.2) a s2 n2 source.memory tempView rfl view.cell
      savedLocal aLocal startLocal sizeLocal returned run
  exact ⟨value, paid, bound, fits, clock, memory, fields⟩

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.saved_normal
