import InitECandidate.Solver.GasBudget.StackPushProgram
import InitECandidate.Solver.Input.ReturnNormal
import Flapjack.Pancake.Semantics.PanProps

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Exact original stack-push store suffix. The actual tuple store derives
all reached writes. Only its four stack words and the real sp cell can change;
there is no body call/loop clock in this suffix. -/
theorem writes_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base sp : BitVec 64)
    (storedValue returned : ValueHOL 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (vLocal : source.locals.lookup (ofString "v") = some storedValue)
    (valueShape : shapeOfHOLExact storedValue = .comb [.one, .one, .one, .one])
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (normal : evaluateHOLFiniteState source writes = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ post.clock = source.clock ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory} ∧
      post.memory (frame + 16#64) = .word (sp + 1#64) ∧
      (∀ address, address ≠ frame + 16#64 →
        (∀ index < 4, address ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index)) →
        post.memory address = source.memory address) := by
  rw [writes_shape] at normal
  have safe : Input.LocalPrefix (ofString "sp") (.store destination (localVar "v")) := .store _ _
  obtain ⟨stored, storeRun, restRun, saved⟩ := safe.normal_continue source post _ returned normal
  have baseRead := frame_read source frame 8#64 base ev baseMapped baseCell
  have addressRead : eval source destination = some (.val (.word (base + sp * 32#64))) := by
    simp only [eval] at baseRead ⊢
    simp only [destination, evalHOLExact, evalListHOLExact, baseRead]
    simp [evalHOLExact, evalListHOLExact, toExact, localVar, spLocal, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
  obtain ⟨actual, memory, valueRead, stores, storedEq⟩ := Input.store_at_normal source stored destination (localVar "v") (base + sp * 32#64) addressRead storeRun
  have actualRead : eval source (localVar "v") = some storedValue := by simpa only [eval, localVar, evalHOLExact, toExact] using vLocal
  have actualEq : actual = storedValue := Option.some.inj (valueRead.symm.trans actualRead)
  subst actual
  have length : (flattenHOL storedValue).length = 4 := by
    have wellFormed : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact storedValue) = true := by rw [valueShape]; decide
    have counted := flattenHOL_length_eq_sizeOfShapeHOL storedValue wellFormed
    rw [valueShape] at counted
    exact counted
  have secondSafe : Input.LocalPrefix (ofString "sp") (.store (frameAddress 16#64) nextSP) := .store _ _
  obtain ⟨done, doneRun, returnRun, savedAgain⟩ := secondSafe.normal_continue stored post _ returned restRun
  have storedSP : stored.locals.lookup (ofString "sp") = some (.val (.word sp)) := by rw [storedEq]; exact spLocal
  have storedEV : stored.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [storedEq]; exact ev
  have nextRead : eval stored nextSP = some (.val (.word (sp + 1#64))) := by
    simp [eval, nextSP, evalHOLExact, evalListHOLExact, localVar, toExact, storedSP, valueIsWord, valueWord, wordOpHOL, wordOp]
  have doneEq := FrameField.normal_word stored done frame 16#64 (sp + 1#64) nextSP storedEV nextRead doneRun
  obtain ⟨returnedRead, postEq⟩ := Input.return_normal done post (.const 0#64) returned returnRun
  have valueEq : returned = .val (.word 0#64) := by
    change some (.val (.word 0#64)) = some returned at returnedRead
    exact (Option.some.inj returnedRead).symm
  have fullEq : post = emptyLocalsHOLFinite {source with memory := StoreWord.put memory (frame + 16#64) (sp + 1#64)} := by
    rw [postEq, doneEq, storedEq]
  refine ⟨valueEq, ?_, ?_, ?_, ?_⟩
  · rw [fullEq]; rfl
  · rw [fullEq]; rfl
  · rw [fullEq]
    change StoreWord.put memory (frame + 16#64) (sp + 1#64) (frame + 16#64) = _
    simp [StoreWord.put]
  · intro address notSP away
    have earlier := Input.words_away (flattenHOL storedValue) (base + sp * 32#64) address source.memaddrs source.memory memory stores
      (by rw [length]; exact away)
    rw [fullEq]
    change StoreWord.put memory (frame + 16#64) (sp + 1#64) address = source.memory address
    rw [show StoreWord.put memory (frame + 16#64) (sp + 1#64) address = memory address from if_neg notSP]
    exact earlier

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.writes_normal
