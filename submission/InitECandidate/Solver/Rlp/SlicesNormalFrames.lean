import InitECandidate.Solver.Rlp.SliceArrayModel
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

theorem Window.bytes_before (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lower upper : Nat) (pointer length : BitVec 64) (frame : Window source target lower upper)
    (before : pointer.toNat+length.toNat≤lower) (fits : pointer.toNat+length.toNat<2^64)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    ReadLength.BytesAgree source target pointer length := by
  intro offset inside
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by omega)
  have backing := WitnessRadix.AllocatedBytes.aligned_number (pointer+offset)
  have memory := frame (panByteAlignHOL (width:=64) (pointer+offset)) (Or.inl (by rw [backing,number]; omega))
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+offset))
  all_goals simp [ReadLength.byte,panMemLoadByteHOL,memory,domain,endian,mapped]

end InitECandidate.Solver.Rlp.Slices

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
