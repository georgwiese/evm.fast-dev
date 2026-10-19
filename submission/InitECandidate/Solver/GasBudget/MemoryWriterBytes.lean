import InitECandidate.Solver.GasBudget.Be32Call

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack PanSemStateFiniteExact WitnessRadix

def BytesMapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat) : Prop :=
  ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset))
def BytesAway (pointer query : BitVec 64) (length : Nat) : Prop :=
  ∀ offset < length, query ≠ panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset)

theorem byte_add (pointer : BitVec 64) (offset index : Nat) :
    (pointer + BitVec.ofNat 64 offset) + BitVec.ofNat 64 index = pointer + BitVec.ofNat 64 (offset + index) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem BytesMapped.subrange {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer : BitVec 64} {length : Nat}
    (mapped : BytesMapped source pointer length) (offset size : Nat) (inside : offset + size ≤ length) :
    BytesMapped source (pointer + BitVec.ofNat 64 offset) size := by
  intro index indexInside
  rw [byte_add]
  exact mapped (offset + index) (by omega)

theorem BytesAway.subrange {pointer query : BitVec 64} {length : Nat} (away : BytesAway pointer query length)
    (offset size : Nat) (inside : offset + size ≤ length) : BytesAway (pointer + BitVec.ofNat 64 offset) query size := by
  intro index indexInside
  rw [byte_add]
  exact away (offset + index) (by omega)

theorem be32_mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer : BitVec 64}
    (mapped : BytesMapped source pointer 4) :
    ∀ clause ∈ Be32Stores.clauses, source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1)) := by
  intro clause member
  have bound : clause.1 < 4 := by
    simp only [Be32Stores.clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  exact mapped clause.1 bound

theorem be32_away {pointer query : BitVec 64} (away : BytesAway pointer query 4) :
    ∀ clause ∈ Be32Stores.clauses, query ≠ panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1) := by
  intro clause member
  have bound : clause.1 < 4 := by
    simp only [Be32Stores.clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  exact away clause.1 bound

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.BytesMapped.subrange
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.BytesAway.subrange
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be32_mapped
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be32_away
