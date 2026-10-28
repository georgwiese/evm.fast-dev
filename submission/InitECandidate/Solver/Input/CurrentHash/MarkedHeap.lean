import InitECandidate.Solver.Input.SavedHeapReturn
import InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost
import InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost
import InitECandidate.Solver.Input.CurrentHash.FixedRecordProgram
import InitECandidate.Solver.Input.CurrentHash.PContainerBitLoop
import InitECandidate.Solver.Input.CurrentHash.PBytesCost
import InitECandidate.Solver.Input.CurrentHash.RequestListLoop
import InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost

namespace InitECandidate.Solver.Input.CurrentHash.MarkedHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open SavedHeapReturn (Tail)

theorem merkle_tail : Tail "mark" MerkleBufferCost.afterMark := by
  rw [MerkleAllocationCost.source_shape.2.1]
  apply Tail.dec "size" .one _ (by decide)
  rw [MerkleAllocationCost.source_shape.2.2]
  apply Tail.decCall "buf" .one _ _ (by decide)
  rw [MerkleBufferCost.source_shape.1]
  apply Tail.ignored_call
  rw [MerkleBufferCost.source_shape.2.1]
  apply Tail.ignored_call
  rw [MerkleBufferCost.source_shape.2.2]
  apply Tail.dec "cur" .one _ (by decide)
  rw [MerkleSuffixCost.source_shape.1]
  apply Tail.seq
  · rw [MerkleDenseCost.source_shape.1]
    exact .loop _ (MerkleDenseCost.other _ (by decide) (by decide) (by decide))
  rw [MerkleSuffixCost.source_shape.2.1]
  apply Tail.dec "d" .one _ (by decide)
  rw [MerkleSuffixCost.source_shape.2.2.1]
  apply Tail.seq
  · rw [(MerklePairLoops.source_shape .extension).1]
    exact .loop _ (MerklePairLoops.other .extension _ (by decide))
  rw [MerkleSuffixCost.source_shape.2.2.2]
  exact Tail.ignored_call _ _ .release

theorem fixed_pipeline (inputName : String) (steps : List FixedRecord.Step) (rest : ProgHOL 64)
    (ending : Tail "mark" rest) : Tail "mark" (FixedRecord.pipeline inputName steps rest) := by
  induction steps with
  | nil => exact ending
  | cons step next ih => exact Tail.ignored_call _ _ ih

theorem fixed_tail (kind : FixedRecord.Kind) : Tail "mark" kind.afterMark := by
  unfold FixedRecord.Kind.afterMark
  apply Tail.decCall "ch" .one _ _ (by decide)
  exact fixed_pipeline kind.inputName kind.steps kind.afterSteps (Tail.ignored_call _ _ .release)

theorem pcontainer_tail : Tail "mark" PContainer.afterMark := by
  rw [PContainer.body_shape.2.1]
  apply Tail.decCall "tmp" .one _ _ (by decide)
  rw [PContainer.body_shape.2.2.1]
  apply Tail.ignored_call
  rw [PContainer.body_shape.2.2.2.1]
  apply Tail.dec "act" .one _ (by decide)
  rw [PContainer.body_shape.2.2.2.2.1]
  apply Tail.ignored_call
  rw [PContainer.body_shape.2.2.2.2.2.1]
  apply Tail.dec "i" .one _ (by decide)
  rw [PContainer.body_shape.2.2.2.2.2.2.1]
  apply Tail.seq
  · rw [PContainer.body_shape.2.2.2.2.2.2.2.1]
    exact .loop _ (PContainer.bit_step_other _ (by decide))
  rw [PContainer.body_shape.2.2.2.2.2.2.2.2.2]
  exact Tail.ignored_call _ _ .release

theorem pbytes_tail : Tail "mark" PBytesCost.afterMark := by
  rw [PBytesCost.source_shape.2.1]
  apply Tail.decCall "pk" PackBytes.returnShape _ _ (by decide)
  rw [PBytesCost.source_shape.2.2.1,PBytesCost.source_shape.2.2.2]
  exact Tail.ignored_call _ _ .release

theorem request_list_tail : Tail "mark" RequestList.afterMark := by
  unfold RequestList.afterMark
  apply Tail.decCall "roots" .one _ _ (by decide)
  unfold RequestList.afterRoots
  apply Tail.dec "i" .one _ (by decide)
  unfold RequestList.loopAndSuffix
  exact .seq (RequestList.loop_local _ (by decide)) (Tail.ignored_call _ _ .release)

theorem progressive_tail : Tail "mark" Progressive.afterMark := by
  rw [ProgressiveBodyCost.prefix_shape.2.1]
  apply Tail.decCall "roots" .one _ _ (by decide)
  rw [ProgressiveBodyCost.prefix_shape.2.2.1]
  apply Tail.decCall "acc" .one _ _ (by decide)
  rw [ProgressiveBodyCost.prefix_shape.2.2.2.1]
  apply Tail.dec "k" .one _ (by decide)
  rw [ProgressiveBodyCost.prefix_shape.2.2.2.2.1]
  apply Tail.dec "off" .one _ (by decide)
  rw [ProgressiveBodyCost.prefix_shape.2.2.2.2.2]
  apply Tail.dec "size" .one _ (by decide)
  rw [Progressive.fold_shape.2.2.1]
  apply Tail.seq
  · rw [Progressive.loop_shape.1]
    exact .loop _ (Progressive.step_other _ (by decide) (by decide) (by decide) (by decide))
  rw [Progressive.fold_shape.2.2.2.1]
  apply Tail.ignored_call
  rw [Progressive.fold_shape.2.2.2.2.1]
  apply Tail.seq
  · rw [Progressive.fold_shape.1]
    exact .loop _ (Progressive.fold_other _ (by decide))
  rw [Progressive.fold_shape.2.2.2.2.2]
  exact Tail.ignored_call _ _ .release

/-- Actual nonempty Merkle work restores its entering heap, without an
intermediate heap, capacity, mapped-input or successful-allocation premise. -/
theorem merkle_nonempty (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source MerkleBufferCost.afterZero = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [MerkleAllocationCost.source_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ merkle_tail installed initial value actual

theorem fixed (kind : FixedRecord.Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source kind.body = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [FixedRecord.body_shape] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ (fixed_tail kind) installed initial value actual

theorem pcontainer (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source PContainer.body = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [PContainer.body_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ pcontainer_tail installed initial value actual

theorem pbytes (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source PBytesCost.body = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [PBytesCost.source_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ pbytes_tail installed initial value actual

theorem request_list (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source RequestList.body = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [RequestList.body_shape] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ request_list_tail installed initial value actual

theorem progressive (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source Progressive.body = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [ProgressiveBodyCost.prefix_shape.1] at actual
  exact SavedHeapReturn.marked_scope source post "mark" heap _ progressive_tail installed initial value actual

end InitECandidate.Solver.Input.CurrentHash.MarkedHeap

#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.merkle_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.fixed_pipeline
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.fixed_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.pcontainer_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.pbytes_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.request_list_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.progressive_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.merkle_nonempty
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.fixed
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.pcontainer
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.pbytes
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.request_list
#print axioms InitECandidate.Solver.Input.CurrentHash.MarkedHeap.progressive
