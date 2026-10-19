import InitECandidate.Solver.GasBudget.FrameExceptionView
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Rebuild the handler from an actual accounted opcode prefix. Its liquid
gas is read from the reached physical state; the unchanged message/snapshot
ownership and conserved ledger suffice even when expansion changed memory. -/
def View.after_accounted {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (view : View source)
    (globals : ∀ key, key ≠ ofString "frame_mem_ptr" → target.globals.lookup key = source.globals.lookup key)
    (domain : target.memaddrs = source.memaddrs)
    (budget : regularBudget target.memory view.frame = regularBudget source.memory view.frame)
    (headers : ∀ offset ∈ ([72, 112, 192] : List Nat), target.memory (view.frame + BitVec.ofNat 64 offset) = source.memory (view.frame + BitVec.ofNat 64 offset))
    (reservoir : target.memory (view.message + 48#64) = source.memory (view.message + 48#64)) : View target := by
  refine ⟨view.frame, view.message, view.continuation, view.empty, wordAt target.memory (view.frame + 64#64), view.spill, view.reservoir,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, view.reservoirAway, view.reservoirOutsideSP, view.continuationAway, ?_, ?_⟩
  · rw [globals _ (by decide)]; exact view.ev
  · rw [globals _ (by decide)]; exact view.curCont
  · rw [globals _ (by decide)]; exact view.emptyGlobal
  · intro offset member
    rw [domain]; exact view.refillMapped offset member
  · intro offset member
    rw [domain]; exact view.haltMapped offset member
  · exact (headers 112 (by simp)).trans view.messageCell
  · exact memory_word _ _
  · exact (headers 192 (by simp)).trans view.spillCell
  · rw [domain]; exact view.reservoirMapped
  · exact reservoir.trans view.reservoirCell
  · rw [domain]; exact view.continuationMapped
  · rw [budget]; exact view.cap

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.View.after_accounted
