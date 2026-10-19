import InitECandidate.Solver.Arenas.ScopedNone
import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current original scratch/frame cursors and fixed ordinary domain.
These entry facts do not assert room for a future record allocation. -/
structure Arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  cursorGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))
  limitGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word limit))
  ordered : limit.toNat≤cursor.toNat
  aligned : limit.toNat%8=0
  lower : 2701131776≤limit.toNat
  upper : cursor.toNat≤33806089496

theorem Arena.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals) : Arena target cursor limit :=
  ⟨domain.trans arena.domain,by rw [globals]; exact arena.cursorGlobal,by rw [globals]; exact arena.limitGlobal,
    arena.ordered,arena.aligned,arena.lower,arena.upper⟩

theorem Arena.record_bounds (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) :
    let pointer := Arenas.rounded .down cursor 24#64
    pointer≠0#64 ∧ pointer.toNat+24<2^64 ∧ pointer.toNat+24≤cursor.toNat ∧
      limit.toNat≤pointer.toNat ∧ pointer.toNat%8=0 := by
  obtain ⟨first,second,lower,upper,padding,aligned⟩ := Arenas.downward_guards cursor limit 24#64 arena.aligned room
  change (Arenas.rounded .down cursor 24#64).toNat+24≤cursor.toNat at upper
  refine ⟨?_,by have := arena.upper; omega,upper,lower,aligned⟩
  intro zero
  rw [zero] at lower
  have := arena.lower
  change _≤0 at lower
  omega

theorem Arena.record_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) (offset : Nat)
    (inside : offset+8≤24) (aligned : offset%8=0) :
    source.memaddrs (Arenas.rounded .down cursor 24#64+BitVec.ofNat 64 offset) := by
  obtain ⟨active,fits,below,lower,pointerAligned⟩ := Arena.record_bounds source cursor limit arena room
  let pointer := Arenas.rounded .down cursor 24#64
  change pointer.toNat+24<2^64 at fits
  change pointer.toNat+24≤cursor.toNat at below
  change limit.toNat≤pointer.toNat at lower
  change pointer.toNat%8=0 at pointerAligned
  have offsetSmall : offset<2^64 := by omega
  have number : (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]; change pointer.toNat+offset<2^64; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  rw [arena.domain]
  apply WitnessRadix.BackingLayout.ordinary_mapped
  · rw [number]; have := arena.lower; change limit.toNat≤pointer.toNat at lower; omega
  · rw [number]; have := arena.upper; change pointer.toNat+24≤cursor.toNat at below; omega
  · rw [number,Nat.add_mod,pointerAligned,aligned]

theorem Arena.after_allocation (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) :
    Arena (Arenas.post source .down cursor 24#64) (Arenas.rounded .down cursor 24#64) limit := by
  obtain ⟨active,fits,below,lower,aligned⟩ := Arena.record_bounds source cursor limit arena room
  refine ⟨arena.domain,?_,?_,lower,arena.aligned,arena.lower,?_⟩
  · simp [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE]
  · simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal
  · have := arena.upper
    omega

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Arena.of_fields
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.record_bounds
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.record_mapped
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.after_allocation
