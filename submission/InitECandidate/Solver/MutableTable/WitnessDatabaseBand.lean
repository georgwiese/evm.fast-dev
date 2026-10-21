import InitECandidate.Solver.MutableTable.WitnessDatabaseBefore

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Preserve exactly the original database's owned band: above its fixed
scratch buffer and below its real allocation frontier. Temporary scratch
writes below the band and fresh heap writes above it are unrestricted. -/
theorem Database.band_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (frontier : Nat) (before : BeforeHeap source table frontier)
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (memory : ∀ query : BitVec 64,scratch.toNat+32≤query.toNat→query.toNat<frontier→target.memory query=source.memory query) :
    Database target array table count maximum slices scratch ∧ BeforeHeap target table frontier := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
  have capSmall : 2^bits<2^64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have capNumber : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  obtain ⟨oldCapacity,oldCell,bound⟩ := before
  have actualCell : source.memory (table+16#64)=.word (BitVec.ofNat 64 (2^bits)) := by
    simpa only [plan,Constructor.allocationPlan,Layout32.parameters,TableEmpty.parameters,BitVec.ofNat_toNat,BitVec.setWidth_eq] using built.header.find.capacity
  have capacityEq : oldCapacity=BitVec.ofNat 64 (2^bits) := HolWordLab.word.inj (oldCell.symm.trans actualCell)
  rw [capacityEq,capNumber] at bound
  have endBefore : plan.table+72+57*plan.capacity+plan.padding≤frontier := bound
  have recordFloor : scratch.toNat+32≤plan.records := actual.footprintFloor
  have recordsBefore:=ready.recordsBefore
  change plan.records+16*plan.count≤plan.table at recordsBefore
  have tableFloor : scratch.toNat+32≤plan.table := by omega
  have tableBefore : plan.table<frontier := by omega
  have finalBuilt:=Layout32.built_of_cells source target plan ready bits scratch stored input logical domain endian
    (by
      intro pool offset inside
      apply Eq.symm
      apply memory
      · rw [Layout32.number plan ready pool offset inside]
        have extent:=Layout32.bounds plan ready pool
        omega
      · rw [Layout32.number plan ready pool offset inside]
        have extent:=Layout32.bounds plan ready pool
        omega) built
  have recordsSame (index offset : Nat) (inside : index<plan.count) (field : offset<16) :
      target.memory (recordCell plan index offset)=source.memory (recordCell plan index offset) := by
    apply memory
    · rw [record_number plan ready index offset inside field]
      omega
    · rw [record_number plan ready index offset inside field]
      omega
  have finalRows : Records target plan slices :=
    ⟨by intro index inside; exact (recordsSame index 0 inside (by decide)).trans (rows.pointers index inside),
      by intro index inside; exact (recordsSame index 8 inside (by decide)).trans (rows.lengths index inside)⟩
  have headerAddress : table+16#64=Layout32.cell plan .header 16 := by
    simpa only [plan,Constructor.allocationPlan,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Layout32.header_cell plan 16
  have headerNumber : (table+16#64).toNat=plan.table+16 := by
    rw [headerAddress,Layout32.number plan ready .header 16 (by change 16<72; decide)]
    rfl
  refine ⟨⟨domain.symm.trans actual.domain,endian.symm.trans actual.little,actual.sizes,
    ⟨bits,stored,input,logical,lower,upper,capacity,ready,finalBuilt,history,length,finalRows⟩,
    actual.arenas,actual.sourceLower,actual.sourceBefore,actual.footprintFloor⟩,BitVec.ofNat 64 (2^bits),?_,?_⟩
  · exact (memory _ (by rw [headerNumber]; omega) (by rw [headerNumber]; omega)).trans actualCell
  · rw [capNumber]
    exact bound

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.band_frame
