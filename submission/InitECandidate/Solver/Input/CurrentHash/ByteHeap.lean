import InitECandidate.Solver.Input.SavedHeapReturn
import InitECandidate.Solver.Input.CurrentHash.PureGlobals
import InitECandidate.Solver.Input.CurrentHash.BytesListCost
import InitECandidate.Solver.Input.CurrentHash.BytesVectorCost

namespace InitECandidate.Solver.Input.CurrentHash.ByteHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open SavedHeapReturn (Tail)

theorem list_tail : Tail "mark" BytesListCost.afterMark := by
  rw [BytesListCost.source_shape.2.1]
  apply Tail.decCall "pk" PackBytes.returnShape _ _ (by decide)
  rw [BytesListCost.source_shape.2.2.1]
  apply Tail.ignored_call
  rw [BytesListCost.source_shape.2.2.2]
  apply Tail.releaseThen
  intro code installed
  exact GlobalEffects.sequence (ofString "heap_ptr") code _ _ (PureGlobals.mix_call _ code installed (some none) _) (GlobalEffects.returned _ code _)

theorem vector_tail : Tail "mark" BytesVectorCost.afterMark := by
  rw [BytesVectorCost.source_shape.2.1]
  apply Tail.decCall "pk" PackBytes.returnShape _ _ (by decide)
  rw [BytesVectorCost.source_shape.2.2.1,BytesVectorCost.source_shape.2.2.2]
  exact Tail.ignored_call _ _ .release

theorem short_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code BytesVectorCost.shortBody := by
  unfold BytesVectorCost.shortBody
  exact GlobalEffects.sequence key code _ _ (MemoryGlobals.call .zero key code installed (some none) _)
    (GlobalEffects.sequence key code _ _ (MemoryGlobals.call .copy key code installed (some none) _) (GlobalEffects.returned key code _))

theorem guard_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code BytesVectorCost.shortGuard :=
  GlobalEffects.conditional key code _ _ _ (short_globals key code installed) (GlobalEffects.skip key code)

theorem vector_long (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source BytesVectorCost.long=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
  rw [BytesVectorCost.source_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ vector_tail installed initial value actual

/-- Both actual byte-vector branches restore the entering heap, with no
length/mapping/workspace premises beyond the same genuine normal return. -/
theorem vector (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source BytesVectorCost.body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
  have frame := guard_globals (ofString "heap_ptr") source.code installed source rfl
  rw [BytesVectorCost.body_shape,evaluateHOLFiniteState_seq_line780] at actual
  generalize observed : evaluateHOLFiniteState source BytesVectorCost.shortGuard=output at actual frame
  obtain ⟨result,middle⟩ := output
  have heapMiddle : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := (congrArg Prod.snd frame).trans initial
  cases result with
  | none =>
    have nextCode : OriginalCode.Installed middle.code := by
      have same := congrArg Prod.fst frame
      change middle.code=source.code at same
      rw [same]
      exact installed
    exact vector_long middle post heap nextCode heapMiddle value actual
  | some result =>
    have endpoint : middle=post := congrArg Prod.snd actual
    rw [←endpoint]
    exact heapMiddle

/-- The real release precedes length mixing. Its checked current mix routine
preserves the restored heap on every outcome. -/
theorem list (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source BytesListCost.body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
  rw [BytesListCost.source_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ list_tail installed initial value actual

end InitECandidate.Solver.Input.CurrentHash.ByteHeap

#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.list_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.vector_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.short_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.guard_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.vector_long
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.vector
#print axioms InitECandidate.Solver.Input.CurrentHash.ByteHeap.list
