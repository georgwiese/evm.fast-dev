import InitECandidate.Solver.MutableTable.WitnessDatabase

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Lookup ownership is independent of the caller's local bindings, clocks
and globals; its actual memory, domain and endianness suffice. -/
theorem Database.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be) :
    Database target array table count maximum slices scratch := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  have finalBuilt:=Layout32.built_fields source target _ bits scratch stored input logical memory domain endian built
  have finalRows : Records target _ slices :=
    ⟨by intro index inside; rw [←memory]; exact rows.pointers index inside,
      by intro index inside; rw [←memory]; exact rows.lengths index inside⟩
  exact ⟨domain.symm.trans actual.domain,endian.symm.trans actual.little,actual.sizes,
    ⟨bits,stored,input,logical,lower,upper,capacity,ready,finalBuilt,history,length,finalRows⟩,actual.arenas,actual.sourceLower,actual.sourceBefore⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.of_fields
