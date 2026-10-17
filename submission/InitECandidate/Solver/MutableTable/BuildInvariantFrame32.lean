import InitECandidate.Solver.MutableTable.InsertBuildCall32
import InitECandidate.Solver.WitnessRadix.MemoryAgreement
import InitECandidate.Solver.WitnessRadix.AllocatedAway

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The original dictionary invariant depends only on actual cells within its
own allocation, rather than all memory in the program. -/
theorem built_of_cells (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (bits : Nat) (scratch : BitVec 64)
    (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (same : ∀ pool offset,offset<size plan pool → source.memory (cell plan pool offset)=target.memory (cell plan pool offset))
    (built : Built bits source plan scratch count input logical) : Built bits target plan scratch count input logical := by
  have headers (offset : Nat) (inside : offset<72) :
      source.memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset)=target.memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    rw [header_cell]
    exact same .header offset inside
  have header : Header target plan scratch count := by
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · intro offset member;rw [←domain];exact built.header.find.mapped offset member
    · exact (headers 16 (by decide)).symm.trans built.header.find.capacity
    · have zeroHeader : source.memory (BitVec.ofNat 64 plan.table)=target.memory (BitVec.ofNat 64 plan.table):=by simpa using headers 0 (by decide)
      exact zeroHeader.symm.trans built.header.find.keyLength
    · exact (headers 8 (by decide)).symm.trans built.header.find.stride
    · exact (headers 32 (by decide)).symm.trans built.header.find.keys
    · exact (headers 48 (by decide)).symm.trans built.header.find.used
    · exact (headers 40 (by decide)).symm.trans built.header.values
    · exact (headers 56 (by decide)).symm.trans built.header.order
    · exact (headers 64 (by decide)).symm.trans built.header.position
    · exact (headers 24 (by decide)).symm.trans built.header.count
  refine ⟨header,⟨?_,?_⟩,?_,built.trace,built.countBound⟩
  · intro index inside
    have read:=MemoryBytes.read_of_cell source target domain endian
      ((parameters plan scratch).used+BitVec.ofNat 64 index) (by
        rw [used_byte_cell plan ready scratch index inside]
        exact same .used (8*(index/8)) (by change 8*(index/8)<plan.capacity;omega))
    change Find.usedByte source (parameters plan scratch) (BitVec.ofNat 64 index)=
      Find.usedByte target (parameters plan scratch) (BitVec.ofNat 64 index) at read
    rw [←read]
    exact built.keys.used index inside
  · intro index inside key value stored
    apply MemoryBytes.byteView_of_cells source target domain endian _ key _ (built.keys.view index inside key value stored)
    intro byte
    rw [key_byte_cell plan ready scratch index byte.val inside byte.isLt]
    exact same .keys (32*index+8*(byte.val/8)) (by change 32*index+8*(byte.val/8)<32*plan.capacity;have:=byte.isLt;omega)
  · intro index inside key value stored
    obtain ⟨mapped,word⟩:=built.values index inside key value stored
    refine ⟨by rw [←domain];exact mapped,?_⟩
    have memory:=same .values (8*index) (by change 8*index<8*plan.capacity;omega)
    rw [←value_cell] at memory
    exact memory.symm.trans word

/-- A later constructor's actual own-memory frame preserves the entire original
map model, when the old allocation follows hash buffers and precedes the new
one. Original and radix private cells can remain different. -/
theorem built_preserved_by_later (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (table : Nat)
    (before : plan.table+72+57*plan.capacity+plan.padding≤table)
    (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136) (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ out.toNat+32≤plan.records)
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (frame : ∀ query,query.toNat<table ∧ Keccak256.Protected stp pad out query → target.memory query=source.memory query)
    (bits : Nat) (scratch : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64))
    (logical : Find.Model32 (BitVec 64)) (built : Built bits source plan scratch count input logical) :
    Built bits target plan scratch count input logical := by
  apply built_of_cells source target plan ready bits scratch count input logical domain endian _ built
  intro pool offset inside
  have address:=number plan ready pool offset inside
  have extent:=bounds plan ready pool
  have recordsBefore:=ready.recordsBefore
  apply Eq.symm
  apply frame
  refine ⟨by rw [address];omega,?_,?_,?_⟩
  · exact AllocatedBytes.Arena.away_above stp _ 200 stateArena (by rw [address];have:=buffersBefore.1;omega)
  · exact AllocatedBytes.Arena.away_above pad _ 136 paddingArena (by rw [address];have:=buffersBefore.2.1;omega)
  · exact AllocatedBytes.Arena.away_above out _ 32 outputArena (by rw [address];have:=buffersBefore.2.2;omega)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.built_of_cells
#print axioms InitECandidate.Solver.MutableTable.Layout32.built_preserved_by_later
