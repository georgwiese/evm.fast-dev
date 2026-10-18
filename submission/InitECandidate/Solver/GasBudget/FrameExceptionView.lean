import InitECandidate.Solver.GasBudget.FrameExceptionInstalled
import InitECandidate.Solver.GasBudget.StackPopPrefixEffect

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current physical frame/message/continuation facts needed by the real
handler. The reservoir is owned outside the active sp cell. -/
structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) where
  frame : BitVec 64
  message : BitVec 64
  continuation : BitVec 64
  empty : BitVec 64
  gas : BitVec 64
  spill : BitVec 64
  reservoir : BitVec 64
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  curCont : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation))
  emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty))
  refillMapped : ∀ offset ∈ ([64, 72, 112, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset)
  haltMapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset)
  messageCell : source.memory (frame + 112#64) = .word message
  gasCell : source.memory (frame + 64#64) = .word gas
  spillCell : source.memory (frame + 192#64) = .word spill
  reservoirMapped : source.memaddrs (message + 48#64)
  reservoirCell : source.memory (message + 48#64) = .word reservoir
  reservoirAway : message + 48#64 ≠ frame + 64#64
  reservoirOutsideSP : message + 48#64 ≠ frame + 16#64
  continuationAway : ∀ offset ∈ ([64, 184, 192] : List Nat), frame + BitVec.ofNat 64 offset ≠ continuation + 32#64
  continuationMapped : source.memaddrs (continuation + 32#64)
  cap : regularBudget source.memory frame ≤ 16777216

/-- Rebuild the actual handler view after a real pre-charge prefix, with no
future physical model assumed. All stored word values are the current ones. -/
def View.after_prefix {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (view : View source) {paid : Nat}
    (effect : StackPop.PrefixEffect source target view.frame paid) : View target := by
  have globals := congrArg PanSemStateFiniteExact.globals effect.fields
  change target.globals = source.globals at globals
  have domain := congrArg PanSemStateFiniteExact.memaddrs effect.fields
  change target.memaddrs = source.memaddrs at domain
  refine ⟨view.frame, view.message, view.continuation, view.empty, view.gas, view.spill, view.reservoir,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, view.reservoirAway, view.reservoirOutsideSP, view.continuationAway, ?_, ?_⟩
  · rw [globals]; exact view.ev
  · rw [globals]; exact view.curCont
  · rw [globals]; exact view.emptyGlobal
  · intro offset member
    rw [domain]; exact view.refillMapped offset member
  · intro offset member
    rw [domain]; exact view.haltMapped offset member
  · exact (effect.outside _ (offsets_ne view.frame 112#64 16#64 (by decide))).trans view.messageCell
  · exact (effect.outside _ (offsets_ne view.frame 64#64 16#64 (by decide))).trans view.gasCell
  · exact (effect.outside _ (offsets_ne view.frame 192#64 16#64 (by decide))).trans view.spillCell
  · rw [domain]; exact view.reservoirMapped
  · exact (effect.outside _ view.reservoirOutsideSP).trans view.reservoirCell
  · rw [domain]; exact view.continuationMapped
  · rw [effect.budget]; exact view.cap

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.View.after_prefix
