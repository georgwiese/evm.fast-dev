import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem View.after_heap_effect {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch)
    (fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite
      {source with globals := target.globals, memory := target.memory, clock := target.clock})
    (globals : HeapGlobals source target)
    (headers : ∀ offset ∈ ([24, 32, 40] : List Nat),
      target.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset)) :
    View target frame base length capacity pointer scratch := by
  have codes := congrArg PanSemStateFiniteExact.code fields
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  change target.code = source.code at codes
  change target.memaddrs = source.memaddrs at domain
  refine ⟨by rw [codes]; exact view.installed,
    (globals (ofString "ev") (by decide)).trans view.ev, ?_,
    (headers 24 (by simp)).trans view.baseCell, (headers 32 (by simp)).trans view.lengthCell,
    (headers 40 (by simp)).trans view.capacityCell, view.depth, view.slack, view.lengthAligned,
    view.capacityAligned, view.baseAligned,
    (globals (ofString "frame_mem_ptr") (by decide)).trans view.pointerGlobal,
    (globals (ofString "scratch_ptr") (by decide)).trans view.scratchGlobal,
    view.cursor, view.ordered, view.scratchAligned, view.frameAbove, view.frameFits, ?_⟩
  · intro offset member
    rw [domain]
    exact view.mapped offset member
  · intro address lower upper aligned
    rw [domain]
    exact view.arena address lower upper aligned

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_heap_effect
