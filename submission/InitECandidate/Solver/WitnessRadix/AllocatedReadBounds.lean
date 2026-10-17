import InitECandidate.Solver.WitnessRadix.AllocatedLayout
import InitECandidate.Solver.WitnessRadix.LayoutLocated
import InitECandidate.Solver.WitnessRadix.AllocatedAway

namespace InitECandidate.Solver.WitnessRadix.AllocatedLayout
open Flapjack BackingLayout

/-- Every actual cell of an allocated witness map lies after its record arena
and before the real final heap cursor, with no address wraparound. -/
theorem cell_bounds (plan : Plan) (ready : Ready plan) (pool : Pool) (offset : Nat)
    (inside : offset<size (layout plan) pool) :
    plan.records≤(cell (layout plan) pool offset).toNat ∧
      (cell (layout plan) pool offset).toNat<plan.table+72+57*plan.capacity+plan.padding := by
  have ext:=extents plan ready pool
  have number:=byteAddress_toNat (base (layout plan) pool) offset (by rw [base_number plan ready pool];omega)
  change plan.records≤(byteAddress _ _).toNat ∧ (byteAddress _ _).toNat<_
  rw [number,base_number plan ready pool]
  have before:=ready.recordsBefore
  cases pool <;> simp only [baseNat,size,layout] at inside ⊢ <;> omega

/-- All protected installed graph words, including record cells and aligned
key limbs, lie within the old map's actual allocation interval. -/
theorem protected_bounds (plan : Plan) (ready : Ready plan) (allocated : Nat) (allocatedBound : allocated≤plan.count)
    (query : BitVec 64) (saved : BackingLayout.Protected (layout plan) allocated query) :
    plan.records≤query.toNat ∧ query.toNat<plan.table+72+57*plan.capacity+plan.padding := by
  have room:=ready.room
  rcases saved with leaf|header|branch
  · rcases leaf with keysHeader|valsHeader|vals|records|keys
    · rw [keysHeader];exact cell_bounds plan ready .header 32 (by change 32<72;decide)
    · rw [valsHeader];exact cell_bounds plan ready .header 40 (by change 40<72;decide)
    · obtain ⟨index,inside,rfl⟩:=vals
      exact cell_bounds plan ready .vals (8*index) (by change index<plan.count at inside;change 8*index<8*plan.capacity;omega)
    · obtain ⟨index,inside,field,fieldBound,rfl⟩:=records
      exact cell_bounds plan ready .records (16*index+8*field) (by change index<plan.count at inside;change 16*index+8*field<16*plan.count;omega)
    · obtain ⟨index,inside,limb,limbBound,rfl⟩:=keys
      exact cell_bounds plan ready .keys (32*index+8*limb) (by change index<plan.count at inside;change 32*index+8*limb<32*plan.capacity;omega)
  · rw [header];exact cell_bounds plan ready .header 24 (by change 24<72;decide)
  · obtain ⟨node,inside,field,fieldBound,rfl⟩:=branch
    exact cell_bounds plan ready .keys (32*(layout plan).count+24*node+8*field)
      (by change 32*plan.count+24*node+8*field<32*plan.capacity;omega)

/-- Earlier installed dictionary words satisfy the real constructor's own-frame
premises when fixed hash buffers precede its records and the new allocation
starts after its final cursor. Earlier private dictionaries need not agree. -/
theorem protected_safe_for_later (plan : Plan) (ready : Ready plan) (allocated table : Nat)
    (allocatedBound : allocated≤plan.count)
    (before : plan.table+72+57*plan.capacity+plan.padding≤table)
    (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136)
    (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ out.toNat+32≤plan.records)
    (query : BitVec 64) (saved : BackingLayout.Protected (layout plan) allocated query) :
    query.toNat<table ∧ Keccak256.Protected stp pad out query := by
  obtain ⟨lower,upper⟩:=protected_bounds plan ready allocated allocatedBound query saved
  refine ⟨by omega,?_,?_,?_⟩
  · exact AllocatedBytes.Arena.away_above stp query 200 stateArena (by have:=buffersBefore.1;omega)
  · exact AllocatedBytes.Arena.away_above pad query 136 paddingArena (by have:=buffersBefore.2.1;omega)
  · exact AllocatedBytes.Arena.away_above out query 32 outputArena (by have:=buffersBefore.2.2;omega)

end InitECandidate.Solver.WitnessRadix.AllocatedLayout

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.cell_bounds
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.protected_bounds
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.protected_safe_for_later
