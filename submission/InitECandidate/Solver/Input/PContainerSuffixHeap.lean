import InitECandidate.Solver.Input.PContainerBodyCost
import InitECandidate.Solver.Input.HeapPrefixReturn
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_loop_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [body_shape.2.2.2.2.2.2.2.2.2] at run
  exact HeapScope.sequence_return_heap source post mark old _ afterSha installed saved heap
    (LocalPrefix.call none _ _ (by intro name impossible; cases impossible)).summary_full
    (GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "sha256_pair") shaArguments ShaFixedCost.pairFormals ShaFixedCost.pairBody .one
      (ShaFixedCost.pair_code source.code installed) (ShaFixedCost.pair_globals (ofString "heap_ptr") source.code installed))
    (fun middle code markLocal heapLocal value remaining=>HeapScope.release_return_heap middle post mark old code markLocal heapLocal value remaining) value run

theorem loop_suffix_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [body_shape.2.2.2.2.2.2.1] at run
  apply HeapScope.sequence_return_heap source post mark old bitLoop afterLoop installed saved heap _ (bit_loop_globals (ofString "heap_ptr") source.code)
    (fun middle code markLocal heapLocal value remaining=>after_loop_return_heap middle post mark old code markLocal heapLocal value remaining) value run
  intro current
  rw [body_shape.2.2.2.2.2.2.2.1]
  exact while_local_summary (ofString "mark") test bitStep (bit_step_summary (ofString "mark") (by decide)) current

theorem after_zero_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [body_shape.2.2.2.2.2.1] at run
  obtain ⟨inner,remaining,endpoint⟩ := declaration_return_word source post "i" (.const 0#64) 0#64 loopAndSuffix value rfl run
  have nextMark := (bind_lookup_other source "i" "mark" 0#64 (by decide)).trans saved
  have restored := loop_suffix_return_heap (bind source "i" 0#64) inner mark old installed nextMark heap value remaining
  rw [endpoint]
  exact restored

theorem after_act_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterAct=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [body_shape.2.2.2.2.1] at run
  exact HeapScope.sequence_return_heap source post mark old _ afterZero installed saved heap
    (LocalPrefix.call none _ _ (by intro name impossible; cases impossible)).summary_full
    (GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code installed) (Zero.globals (ofString "heap_ptr") source.code))
    (fun middle code markLocal heapLocal value remaining=>after_zero_return_heap middle post mark old code markLocal heapLocal value remaining) value run

theorem after_progressive_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterProgressive=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have read : eval source (.op .add [localVar "tmp",.const 32#64])=some (.val (.word (tmp+32#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,temporary,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [body_shape.2.2.2.1] at run
  obtain ⟨inner,remaining,endpoint⟩ := declaration_return_word source post "act" _ (tmp+32#64) afterAct value read run
  have nextMark := (bind_lookup_other source "act" "mark" (tmp+32#64) (by decide)).trans saved
  have restored := after_act_return_heap (bind source "act" (tmp+32#64)) inner mark old installed nextMark heap value remaining
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_loop_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.loop_suffix_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.after_zero_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.after_act_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.after_progressive_return_heap
