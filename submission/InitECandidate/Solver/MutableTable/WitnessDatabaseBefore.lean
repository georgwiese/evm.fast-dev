import InitECandidate.Solver.MutableTable.WitnessDatabaseFields

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A frontier for this immutable table, tied to its actual physical
capacity header. It can be transported while later allocations advance. -/
def BeforeHeap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (frontier : Nat) : Prop :=
  ∃ capacity : BitVec 64,source.memory (table+16#64)=.word capacity ∧
    table.toNat+72+57*capacity.toNat+Constructor.padding capacity.toNat≤frontier

/-- The original constructor's exact returned heap lies after its table. -/
theorem Normal.before_heap (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count : Nat) (stp pad scratch : BitVec 64) (actual : Normal source target array heap count stp pad scratch) :
    ∃ current,target.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) ∧ BeforeHeap target heap current.toNat := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,built,history,length,ready,heapCell⟩ := actual.table
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  have endSmall : plan.table+72+57*plan.capacity+plan.padding<2^64 := by
    have h:=ready.fits
    change plan.table+72+57*plan.capacity+plan.padding≤33806089496 at h
    omega
  have capSmall : 2^bits<2^64 := by have h:=ready.fits; change plan.table+72+57*(2^bits)+plan.padding≤33806089496 at h; omega
  have capNumber : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  refine ⟨BitVec.ofNat 64 (plan.table+72+57*plan.capacity+plan.padding),heapCell,BitVec.ofNat 64 (2^bits),?_,?_⟩
  · simpa only [plan,Constructor.allocationPlan,Layout32.parameters,TableEmpty.parameters,BitVec.ofNat_toNat,BitVec.setWidth_eq] using built.header.find.capacity
  · rw [capNumber]
    have endNumber : (BitVec.ofNat 64 (plan.table+72+57*plan.capacity+plan.padding)).toNat=plan.table+72+57*plan.capacity+plan.padding := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt endSmall]
    rw [endNumber]
    exact Nat.le_refl _

/-- An earlier-memory frame preserves both the full genuine database and
its physical allocation frontier. Only actual owned cells are read. -/
theorem Database.before_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (frontier : Nat) (before : BeforeHeap source table frontier)
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (memory : ∀ query : BitVec 64,query.toNat<frontier→target.memory query=source.memory query) :
    Database target array table count maximum slices scratch ∧ BeforeHeap target table frontier := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
  have capSmall : 2^bits<2^64 := by have h:=ready.fits; change plan.table+72+57*(2^bits)+plan.padding≤33806089496 at h; omega
  have capNumber : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  obtain ⟨oldCapacity,oldCell,bound⟩ := before
  have actualCell : source.memory (table+16#64)=.word (BitVec.ofNat 64 (2^bits)) := by
    simpa only [plan,Constructor.allocationPlan,Layout32.parameters,TableEmpty.parameters,BitVec.ofNat_toNat,BitVec.setWidth_eq] using built.header.find.capacity
  have capacityEq : oldCapacity=BitVec.ofNat 64 (2^bits) := by
    have equal:=oldCell.symm.trans actualCell
    cases equal
    rfl
  rw [capacityEq,capNumber] at bound
  have endBefore : plan.table+72+57*plan.capacity+plan.padding≤frontier := bound
  have finalBuilt:=Layout32.built_of_cells source target plan ready bits scratch stored input logical domain endian
    (by
      intro pool offset inside
      apply Eq.symm
      apply memory
      rw [Layout32.number plan ready pool offset inside]
      have extent:=Layout32.bounds plan ready pool
      omega) built
  have finalRows:=Records.of_earlier source target plan ready slices
    (by intro query earlier; apply memory; omega) rows
  refine ⟨⟨domain.symm.trans actual.domain,endian.symm.trans actual.little,actual.sizes,
    ⟨bits,stored,input,logical,lower,upper,capacity,ready,finalBuilt,history,length,finalRows⟩,actual.arenas,actual.sourceLower,actual.sourceBefore⟩,
    BitVec.ofNat 64 (2^bits),?_,?_⟩
  · have number:=byteAddress_toNat table 16 (by have h:=ready.fits; change table.toNat+72+57*plan.capacity+plan.padding≤33806089496 at h; omega)
    exact (memory _ (by change (byteAddress table 16).toNat<frontier; rw [number]; omega)).trans actualCell
  · rw [capNumber]
    exact bound

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.before_heap
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.before_frame
