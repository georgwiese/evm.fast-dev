import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Final

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem second_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame current temporary : BitVec 64) (a : BitVec 64 × BitVec 64) (s2 n2 : U256Value.Words)
    (original : WordWrites.Memory) (view : MemoryExpansionCost.View source frame temporary)
    (image : source.memory = StoreWord.put original (frame + 32#64) temporary)
    (oldCell : original (frame + 32#64) = .word current)
    (savedLocal : source.locals.lookup (ofString "saved") = some (.val (.word current)))
    (aLocal : source.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a))
    (startLocal : source.locals.lookup (ofString "s2") = some (U256Value.tuple s2))
    (sizeLocal : source.locals.lookup (ofString "n2") = some (U256Value.tuple n2))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source afterTemporary = (some (.returned returned), post)) :
    returned = MemoryExpansionCost.pairValue (merge a (MemoryExpansionCost.resultPair s2 n2 temporary)) ∧
      ∃ paid : Nat, paid ≤ 21 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        post.memory = original ∧ Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := original} := by
  rw [afterTemporary] at run
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "s2", localVar "n2"] = some [U256Value.tuple s2, U256Value.tuple n2] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, startLocal, sizeLocal]
  obtain ⟨paid, ready, inner, positive, bound, fits, readyEq, fields, tailRun, scopeEq⟩ :=
    MemoryExpansionCost.normal_prefix source post frame temporary s2 n2 view "b" [localVar "s2", localVar "n2"] afterB returned args run
  have readyView := view.after_erase fields
  have readySaved := (Input.KnownUnaryPrefix.lookup_other readyEq "saved" (by decide)).trans savedLocal
  have readyA := (Input.KnownUnaryPrefix.lookup_other readyEq "a" (by decide)).trans aLocal
  have readyB := Input.KnownUnaryPrefix.lookup_same readyEq
  have actual := final_execute ready frame current a (MemoryExpansionCost.resultPair s2 n2 temporary)
    readyView.ev readyView.mapped readySaved readyA readyB
  have same := tailRun.symm.trans actual
  have value : returned = MemoryExpansionCost.pairValue (merge a (MemoryExpansionCost.resultPair s2 n2 temporary)) :=
    PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have innerEq : inner = emptyLocalsHOLFinite {ready with memory := StoreWord.put ready.memory (frame + 32#64) current} := congrArg Prod.snd same
  have readyMemory := Input.LocalEffects.memory_of_erase source ready fields
  have restored : StoreWord.put ready.memory (frame + 32#64) current = original := by
    rw [readyMemory, image]
    exact restore_memory original _ current temporary oldCell
  have memory : post.memory = original := by
    rw [scopeEq, innerEq]
    change StoreWord.put ready.memory (frame + 32#64) current = _
    exact restored
  refine ⟨value, paid, bound, fits, ?_, memory, ?_⟩
  · rw [scopeEq, innerEq]
    change ready.clock = _
    rw [readyEq]
    rfl
  · have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => Input.LocalEffects.erase {state with memory := original}) fields
    rw [scopeEq, innerEq]
    change Input.LocalEffects.erase {ready with memory := StoreWord.put ready.memory (frame + 32#64) current} = _
    rw [restored]
    exact lifted

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.second_normal
