import InitECandidate.Solver.Rlp.SlicesWindowBytes
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Arena.heap_updated (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit nextHeap : BitVec 64)
    (arena : Arena source cursor limit) (domain : target.memaddrs=source.memaddrs)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word nextHeap))) : Arena target cursor limit := by
  refine ⟨domain.trans arena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  · rw [globals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.cursorGlobal
  · rw [globals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Slices.Window.bytes_before
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.heap_updated
