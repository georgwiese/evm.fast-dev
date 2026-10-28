import InitECandidate.Solver.Input.CurrentHash.PayloadStaticProgram
import InitECandidate.Solver.Input.SavedHeapReturn

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open SavedHeapReturn (Tail)

theorem static_tail (fields : List StaticFields.Field) (rest : ProgHOL 64) (ending : Tail "mark" rest) : Tail "mark" (StaticFields.program fields rest) := by
  induction fields with
  | nil=>exact ending
  | cons field rest ih=>exact Tail.ignored_call _ _ ih

theorem final_tail : Tail "mark" finalFields := by
  rw [StaticFields.final_shape]
  apply static_tail
  exact Tail.ignored_call _ _ (Tail.ignored_call _ _ (Tail.ignored_call _ _ .release))

theorem withdrawal_tail : Tail "mark" withdrawalScope := by
  rw [withdrawal_shapes.1]
  apply Tail.dec "wd" .one _ (by decide)
  rw [withdrawal_shapes.2.1]
  apply Tail.dec "nwd" .one _ (by decide)
  rw [withdrawal_shapes.2.2.1]
  apply Tail.seq
  · exact .call (some (ofString "roots")) _ _ (by intro name equal; cases equal; decide)
  rw [withdrawal_shapes.2.2.2.1]
  apply Tail.seq (.assign _ _ (by decide))
  rw [withdrawal_shapes.2.2.2.2.1]
  apply Tail.seq
  · rw [loop_shapes.2.2.1]
    exact .loop _ (withdrawal_step_local _ (by decide))
  rw [withdrawal_shapes.2.2.2.2.2.1]
  apply Tail.ignored_call
  rw [withdrawal_shapes.2.2.2.2.2.2]
  exact Tail.ignored_call _ _ final_tail

theorem transaction_tail : Tail "mark" transactionScope := by
  rw [transaction_shapes.1]
  apply Tail.dec "txs" .one _ (by decide)
  rw [transaction_shapes.2.1]
  apply Tail.dec "ntx" .one _ (by decide)
  rw [transaction_shapes.2.2.1]
  apply Tail.decCall "m2" .one _ _ (by decide)
  rw [transaction_shapes.2.2.2.1]
  apply Tail.decCall "roots" .one _ _ (by decide)
  rw [transaction_shapes.2.2.2.2.1]
  apply Tail.dec "i" .one _ (by decide)
  rw [transaction_shapes.2.2.2.2.2.1]
  apply Tail.seq
  · rw [loop_shapes.1]
    exact .loop _ (transaction_step_local _ (by decide))
  rw [transaction_shapes.2.2.2.2.2.2.1]
  apply Tail.ignored_call
  rw [transaction_shapes.2.2.2.2.2.2.2]
  exact Tail.ignored_call _ _ withdrawal_tail

theorem after_chunks_tail : Tail "mark" afterChunks := by
  rw [StaticFields.prefix_shape]
  apply static_tail
  apply Tail.ignored_call
  exact static_tail _ _ transaction_tail

theorem after_mark_tail : Tail "mark" afterMark := by
  rw [entry_shapes.2.2]
  exact Tail.decCall "ch" .one _ _ (by decide) after_chunks_tail

/-- Current payload hashing restores its entering heap through both dynamic
loops and actual m2 releases. Counts, input/workspace mapping, intermediate
heap values and additional allocation room are not entry premises. -/
theorem body_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [entry_shapes.1] at actual
  obtain ⟨declared,inner,read,shape,remaining,endpoint⟩ := CallNormal.declaration_normal_entry source post "raw" .one (fieldExpression 0) afterRaw value actual
  let entry := setVarHOLFinite (ofString "raw") declared source
  rw [entry_shapes.2.1] at remaining
  have restored := SavedHeapReturn.marked_scope entry inner "mark" cursor afterMark after_mark_tail installed heap value remaining
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.static_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.final_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.withdrawal_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.transaction_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.after_chunks_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.after_mark_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.body_heap
