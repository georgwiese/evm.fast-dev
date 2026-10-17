import InitECandidate.Solver.GasBudget.FrameOpenRecord

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack

/-- Both sides of the continuation allocation are unchanged, including the
child, earlier scratch allocations and persistent memory. -/
theorem record_memory_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower child parent continuation kind message query : BitVec 64)
    (lowerAligned : lower.toNat % 8 = 0) (room : lower.toNat + 104 ≤ scratch.toNat)
    (outside : Arenas.Outside lower scratch query) :
    (recordClosed source scratch child parent continuation kind message).memory query = source.memory query := by
  have geometry := Arenas.downward_guards scratch lower 104#64 lowerAligned room
  have startBound : lower.toNat ≤ (recordPointer scratch).toNat := geometry.2.2.1
  have endBound : (recordPointer scratch).toNat + 104 ≤ scratch.toNat := geometry.2.2.2.1
  have away (offset : Nat) (inside : offset < size) : query ≠ WitnessRadix.byteAddress (recordPointer scratch) offset := by
    change offset < 104 at inside
    have number := WitnessRadix.byteAddress_toNat (recordPointer scratch) offset (by have bound := scratch.isLt; omega)
    intro same
    have equal := congrArg BitVec.toNat same
    rw [number] at equal
    rcases outside with below | high <;> omega
  change WitnessRadix.WordWrites.write (WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size)
    (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)) query = source.memory query
  rw [WitnessRadix.WordWrites.write_away]
  · exact WitnessRadix.Zero.final_memory_away source.memory (recordPointer scratch) query size away
  · simp only [FieldStores.writes, recordFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨away 0 (by decide), away 8 (by decide), away 16 (by decide), away 40 (by decide)⟩

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.record_memory_outside
