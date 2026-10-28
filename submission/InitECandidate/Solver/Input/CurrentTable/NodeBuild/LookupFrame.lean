import InitECandidate.Solver.Input.CurrentTable.NodeBuild.StateTransport
import InitECandidate.Solver.Input.CurrentTable.ImageIntervalFrame

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact

/-- Lookup needs only the actual physical table interval. Unrelated global
updates, including state_init's ws binding, do not invalidate this image. -/
theorem ImageUpTo.of_interval {data : Data} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {processed : Nat} (table : ImageUpTo data source processed)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ address : BitVec 64,data.table.toNat≤address.toNat →
      address.toNat<(New.endPointer data.table data.cap).toNat → target.memory address=source.memory address) :
    ImageUpTo data target processed := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := table
  exact ⟨root,next,count,valid,bits,left,right,keys,image.of_interval domain endian ⟨memory⟩,bound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.ImageUpTo.of_interval
