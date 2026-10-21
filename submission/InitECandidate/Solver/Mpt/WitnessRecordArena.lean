import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def pointer (cursor : BitVec 64) : BitVec 64:=Arenas.rounded .down cursor 88#64

/-- Real room for the original88-byte record derives its aligned fresh
arena below the actual current scratch cursor and above its live limit. -/
theorem allocation_bounds (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64) :
    AllocatedBytes.Arena (pointer cursor) 88 ∧ limit.toNat≤(pointer cursor).toNat ∧
      (pointer cursor).toNat+88≤cursor.toNat ∧ (pointer cursor).toNat%8=0 ∧ pointer cursor≠0#64 := by
  obtain ⟨first,second,lower,upper,padding,aligned⟩:=Arenas.downward_guards cursor limit 88#64 arena.aligned room
  change limit.toNat≤(pointer cursor).toNat at lower
  change (pointer cursor).toNat+88≤cursor.toNat at upper
  change (pointer cursor).toNat%8=0 at aligned
  have buffer : AllocatedBytes.Arena (pointer cursor) 88:=⟨by have bound:=arena.lower; omega,by have bound:=arena.upper; omega⟩
  refine ⟨buffer,lower,upper,aligned,?_⟩
  intro zero
  rw [zero] at lower
  have bound:=arena.lower
  change limit.toNat≤0 at lower
  omega

theorem allocation_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (offset : Nat) (inside : offset<88) (aligned : offset%8=0) : source.memaddrs (byteAddress (pointer cursor) offset) := by
  obtain ⟨buffer,lower,upper,pointerAligned,active⟩:=allocation_bounds source cursor limit arena room
  exact AllocatedBytes.word_mapped source (pointer cursor) 88 offset arena.domain buffer inside pointerAligned aligned

/-- The current fixed-limit record allowance decreases on the genuine
allocation, even if rounding consumes additional bytes. -/
theorem allowance_decreases (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64) :
    ((pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 := by
  obtain ⟨buffer,lower,upper,aligned,active⟩:=allocation_bounds source cursor limit arena room
  omega

theorem after_allocation (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64) :
    Rlp.Validation.Arena (Arenas.post source .down cursor 88#64) (pointer cursor) limit := by
  obtain ⟨buffer,lower,upper,aligned,active⟩:=allocation_bounds source cursor limit arena room
  refine ⟨arena.domain,?_,?_,lower,arena.aligned,arena.lower,by have bound:=arena.upper; omega⟩
  · simp [Arenas.post,Arenas.pointerName,pointer,HolFiniteMapExact.update,FUPDATE]
  · simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,show ofString "scratch_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.allocation_bounds
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.allocation_mapped
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.allowance_decreases
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.after_allocation
