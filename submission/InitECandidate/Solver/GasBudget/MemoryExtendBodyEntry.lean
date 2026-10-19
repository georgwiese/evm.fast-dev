import InitECandidate.Solver.GasBudget.MemoryExtendTailView
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem body_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand : BitVec 64) (returned : ValueHOL 64)
    (view : View source frame base length capacity pointer scratch)
    (expandLocal : source.locals.lookup (ofString "expand_by") = some (.val (.word expand)))
    (nonzero : expand ≠ 0#64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ ready inner, Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧ ready.clock = source.clock ∧
      ready.locals.lookup (ofString "len") = some (.val (.word length)) ∧
      ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      ready.locals.lookup (ofString "expand_by") = some (.val (.word expand)) ∧
      ready.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))) ∧
      evaluateHOLFiniteState ready afterNewLength = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  have guard : evaluateHOLFiniteState source zeroGuard = (none, source) := by
    simp [zeroGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
      expandLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
  rw [body_shape, StateSteps.next_sequence source source zeroGuard afterZero guard (Nat.le_refl _)] at normal
  obtain ⟨firstPost, firstRun, firstScope⟩ := Input.declaration_return_word source post "len" (frameLoad 32#64) length afterLength returned
    (frame_read source frame 32#64 length view.ev (view.mapped 32 (by simp)) view.lengthCell) normal
  let first := WitnessRadix.QueryBranch.bind source "len" length
  have firstView : View first frame base length capacity pointer scratch := view.after_erase rfl
  obtain ⟨secondPost, secondRun, secondScope⟩ := Input.declaration_return_word first firstPost "cap" (frameLoad 40#64) capacity afterCapacity returned
    (frame_read first frame 40#64 capacity firstView.ev (firstView.mapped 40 (by simp)) firstView.capacityCell) firstRun
  let second := WitnessRadix.QueryBranch.bind first "cap" capacity
  have secondLength : second.locals.lookup (ofString "len") = some (.val (.word length)) :=
    (bind_lookup_other first "cap" "len" _ (by decide)).trans (bind_lookup_same source "len" length)
  have sumRead : eval second (.op .add [localVar "len", localVar "expand_by"]) = some (.val (.word (newLength length expand))) := by
    have secondExpand : second.locals.lookup (ofString "expand_by") = some (.val (.word expand)) :=
      (bind_lookup_other first "cap" "expand_by" _ (by decide)).trans
        ((bind_lookup_other source "len" "expand_by" _ (by decide)).trans expandLocal)
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, secondLength, secondExpand, newLength, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨inner, innerRun, innerScope⟩ := Input.declaration_return_word second secondPost "nlen" _ (newLength length expand) afterNewLength returned sumRead secondRun
  let ready := WitnessRadix.QueryBranch.bind second "nlen" (newLength length expand)
  refine ⟨ready, inner, rfl, rfl, ?_, ?_, ?_, bind_lookup_same _ _ _, innerRun, ?_, ?_⟩
  · exact (bind_lookup_other second "nlen" "len" _ (by decide)).trans secondLength
  · exact (bind_lookup_other second "nlen" "cap" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other second "nlen" "expand_by" _ (by decide)).trans
      ((bind_lookup_other first "cap" "expand_by" _ (by decide)).trans
        ((bind_lookup_other source "len" "expand_by" _ (by decide)).trans expandLocal))
  · rw [firstScope, secondScope, innerScope]; rfl
  · rw [firstScope, secondScope, innerScope]; rfl

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.body_entry
