import InitECandidate.Solver.Mpt.CompactToNibblesCurrentSnapshot
import InitECandidate.Solver.Input.PersistentNormalFrame

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Input Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Retain the complete runtime, nonheap globals and all earlier words
from the actual compact conversion snapshot. -/
theorem CurrentSnapshot.persistent_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {length nibbles : Nat} {heap leaf : BitVec 64}
    (snapshot : CurrentSnapshot source target length heap nibbles leaf) : PersistentNormalFrame source target heap := by
  have globals:=congrArg PanSemStateFiniteExact.globals snapshot.metadata
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))).globals at globals
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase {state with globals:=source.globals}) snapshot.metadata
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source at metadata
  exact ⟨⟨_,snapshot.heapCell,snapshot.nextArena,snapshot.nextBound,snapshot.nextAligned,by have grows:=snapshot.grows; omega⟩,metadata,
    by intro key other; rw [globals]; simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other],
    fun query before=>snapshot.memory query (Or.inl before)⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.CurrentSnapshot.persistent_frame
