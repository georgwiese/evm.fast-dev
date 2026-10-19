import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.FrameExceptionHandlerMemory

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem View.after_handler (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (handler : FrameException.View source) (base length capacity pointer scratch err : BitVec 64)
    (view : View source handler.frame base length capacity pointer scratch)
    (apart : ∀ offset ∈ ([24, 32, 40] : List Nat), handler.frame + BitVec.ofNat 64 offset ≠ handler.continuation + 32#64)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, post)) :
    View post handler.frame base length capacity pointer scratch := by
  have memory := FrameException.handler_memory source post handler err view.installed errLocal normal
  obtain ⟨funded, bounded, clock, canonical, budget, done⟩ := FrameException.handler_normal source post handler err view.installed errLocal normal
  have headers (offset : Nat) (member : offset ∈ ([24, 32, 40] : List Nat)) :
      post.memory (handler.frame + BitVec.ofNat 64 offset) = source.memory (handler.frame + BitVec.ofNat 64 offset) := by
    rw [memory]
    apply FrameException.memory_after_away _ _ _ _ _ _ _ _ _ _ (apart offset member)
    intro field inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals simp only [FrameException.writeOffsets, List.mem_cons, List.not_mem_nil, or_false] at inside
    all_goals rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact offsets_ne handler.frame _ _ (by decide)
  have current := view.with_memory post.memory ((headers 24 (by simp)).trans view.baseCell)
    ((headers 32 (by simp)).trans view.lengthCell) ((headers 40 (by simp)).trans view.capacityCell)
  apply current.after_erase
  rw [canonical]
  rfl

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_handler
