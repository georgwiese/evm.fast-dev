import InitECandidate.Solver.Input.CurrentTable.KeyCopy

namespace InitECandidate.Solver.Input.CurrentTable.KeyCopy
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst query : BitVec 64)
    (away : ∀ limb : Fin 4,query ≠ dst+BitVec.ofNat 64 (8*limb.val)) :
    (result source src dst).memory query = source.memory query := by
  apply WordWrites.write_away
  simp only [Copy32.writes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨by simpa using away ⟨0,by decide⟩,away ⟨1,by decide⟩,away ⟨2,by decide⟩,away ⟨3,by decide⟩⟩

/-- The exact four key-copy writes preserve every earlier physical word. -/
theorem memory_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst query : BitVec 64)
    (arena : AllocatedBytes.Arena dst 32) (before : query.toNat < dst.toNat) :
    (result source src dst).memory query = source.memory query := by
  apply memory_away
  intro limb same
  have bound : 8*limb.val < 32 := by have := limb.isLt; omega
  have number := byteAddress_toNat dst (8*limb.val) (by have := arena.upper; omega)
  change (dst+BitVec.ofNat 64 (8*limb.val)).toNat = dst.toNat+8*limb.val at number
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  omega

end InitECandidate.Solver.Input.CurrentTable.KeyCopy

#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.memory_away
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.memory_before
