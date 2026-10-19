import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.Input.HeapScope

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem View.with_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (heap : BitVec 64) :
    View (Input.HeapScope.releasePost source heap) frame base length capacity pointer scratch := by
  refine ⟨view.installed, ?_, view.mapped, view.baseCell, view.lengthCell, view.capacityCell, view.depth, view.slack,
    view.lengthAligned, view.capacityAligned, view.baseAligned, ?_, ?_, view.cursor, view.ordered,
    view.scratchAligned, view.frameAbove, view.frameFits, view.arena⟩
  all_goals simpa [Input.HeapScope.releasePost, HolFiniteMapExact.update, FUPDATE, ofString] using
    (by first | exact view.ev | exact view.pointerGlobal | exact view.scratchGlobal)

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.with_heap
