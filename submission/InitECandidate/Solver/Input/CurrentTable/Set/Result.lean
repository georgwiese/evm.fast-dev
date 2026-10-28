import InitECandidate.Solver.Input.CurrentTable.Image
import InitECandidate.Solver.Input.MemoryMetadata

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A real insertion result for the builder: a full current image with
at most one additional leaf, all nonmemory physical fields retained and
every earlier decoded-input word protected. -/
structure Result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64) (count : Nat) (ValueOf : BitVec 64 → Prop) : Prop where
  image : ∃ root next afterCount valid bits left right keys,
    Image post table cap root next afterCount valid bits left right keys ValueOf ∧ afterCount ≤ count+1
  metadata : MemoryMetadata.erase post = MemoryMetadata.erase source
  before : ∀ address : BitVec 64,address.toNat < table.toNat → post.memory address = source.memory address

theorem Result.of_frames {origin source post target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap : BitVec 64}
    {count : Nat} {ValueOf : BitVec 64 → Prop} (result : Result source post table cap count ValueOf)
    (entry : LocalEffects.erase source = LocalEffects.erase origin) (exit : LocalEffects.erase target = LocalEffects.erase post) :
    Result origin target table cap count ValueOf := by
  obtain ⟨root,next,afterCount,valid,bits,left,right,keys,image,bound⟩ := result.image
  refine ⟨⟨root,next,afterCount,valid,bits,left,right,keys,image.of_frame exit,bound⟩,
    (MemoryMetadata.of_frame exit).trans (result.metadata.trans (MemoryMetadata.of_frame entry)),?_⟩
  intro address before
  rw [LocalEffects.memory_of_erase _ _ exit,result.before address before,LocalEffects.memory_of_erase _ _ entry]

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Result.of_frames
