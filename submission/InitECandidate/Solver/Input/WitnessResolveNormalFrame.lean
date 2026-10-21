import InitECandidate.Solver.Mpt.WitnessResolveFrame
import InitECandidate.Solver.Rlp.ValidationWriteFrame

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical state retained by a genuine original resolver return.
The scratch cursor is restored; only a fresh hashed node may advance the
heap. All old record, array, node and database words above cursor survive. -/
structure ResolveFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat
  arena : Rlp.Validation.Arena target cursor limit
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : ∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key
  memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<heap.toNat→target.memory query=source.memory query

theorem ResolveFrame.of_erase (source target current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : ResolveFrame source current heap cursor limit) (pure : LocalEffects.erase target=LocalEffects.erase current) :
    ResolveFrame source target heap cursor limit := by
  have memory:=LocalEffects.memory_of_erase current target pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  have endian:=congrArg PanSemStateFiniteExact.be pure
  have codeEq:=congrArg PanSemStateFiniteExact.code pure
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=current.globals at globals
  obtain ⟨next,cell,arena,aligned,grows⟩:=frame.nextHeap
  exact ⟨⟨next,by rw [globals]; exact cell,arena,aligned,grows⟩,
    frame.arena.of_fields current target cursor limit domain globals,domain.trans frame.domain,endian.trans frame.endian,codeEq.trans frame.code,
    by intro key other; rw [globals]; exact frame.globals key other,
    by intro query above below; rw [memory]; exact frame.memory query above below⟩

theorem ResolveFrame.unchanged (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (arena : Rlp.Validation.Arena source cursor limit)
    (pure : LocalEffects.erase target=LocalEffects.erase source) : ResolveFrame source target heap cursor limit := by
  have frame : ResolveFrame source source heap cursor limit:=
    ⟨⟨heap,heapCell,heapArena,aligned,Nat.le_refl _⟩,arena,rfl,rfl,rfl,by intros; rfl,by intros; rfl⟩
  exact frame.of_erase source target source heap cursor limit pure

theorem ResolveFrame.hashed (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash cursor limit : BitVec 64)
    (nodeArena : AllocatedBytes.Arena heap 32) (aligned : heap.toNat%8=0) (arena : Rlp.Validation.Arena source cursor limit)
    (pure : LocalEffects.erase target=LocalEffects.erase (Mpt.WitnessResolve.hashAllocated source heap hash)) :
    ResolveFrame source target heap cursor limit := by
  obtain ⟨heapCell,heapArena,heapAligned,grows⟩:=Mpt.WitnessResolve.hash_allocated_heap source heap hash nodeArena
  have frame : ResolveFrame source (Mpt.WitnessResolve.hashAllocated source heap hash) heap cursor limit:=
    ⟨⟨PersistentAlloc.rounded heap 32#64,heapCell,heapArena,heapAligned,by omega⟩,
      Mpt.WitnessResolve.hash_allocated_arena source heap hash cursor limit arena,rfl,rfl,rfl,
      Mpt.WitnessResolve.hash_allocated_global source heap hash,
      by intro query above below; exact Mpt.WitnessResolve.hash_allocated_memory source heap hash nodeArena aligned query (Or.inl below)⟩
  exact frame.of_erase source target _ heap cursor limit pure

/-- Compose the genuine read-only-above-cursor parser prefix with the
actual resolver suffix frame, retaining the same incoming heap frontier. -/
theorem ResolveFrame.prefix (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : ResolveFrame middle target heap cursor limit)
    (domain : middle.memaddrs=source.memaddrs) (endian : middle.be=source.be) (codeEq : middle.code=source.code)
    (globals : ∀ key,middle.globals.lookup key=source.globals.lookup key)
    (above : Rlp.Validation.Above source middle cursor.toNat) : ResolveFrame source target heap cursor limit :=
  ⟨frame.nextHeap,frame.arena,frame.domain.trans domain,frame.endian.trans endian,frame.code.trans codeEq,
    fun key other=>(frame.globals key other).trans (globals key),fun query lower upper=>(frame.memory query lower upper).trans (above query lower)⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveFrame.of_erase
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveFrame.unchanged
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveFrame.hashed
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveFrame.prefix
