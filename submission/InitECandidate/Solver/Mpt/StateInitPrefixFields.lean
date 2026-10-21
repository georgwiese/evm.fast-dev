import InitECandidate.Solver.Mpt.StateInitPrefix

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem ready_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64) :
    (ready source heap nodes root codes).clock=source.clock-1 := rfl

/-- Actual workspace initialization protects all earlier allocated memory. -/
theorem ready_earlier (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 40) (earlier : query.toNat<heap.toNat) :
    (ready source heap nodes root codes).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset<40) : query≠heap+BitVec.ofNat 64 offset := by
    have number:=byteAddress_toNat heap offset (by have h:=arena.upper; omega)
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    change query.toNat=(byteAddress heap offset).toNat at numeric
    rw [number] at numeric
    omega
  simp only [ready,written,StoreWord.put,if_neg (away 16 (by decide)),if_neg (away 8 (by decide)),if_neg (away 0 (by decide))]
  rfl

/-- The genuine three stored fields are retained at the materializer entry. -/
theorem ready_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64)
    (arena : AllocatedBytes.Arena heap 40) :
    (ready source heap nodes root codes).memory heap=.word nodes ∧
    (ready source heap nodes root codes).memory (heap+8#64)=.word root ∧
    (ready source heap nodes root codes).memory (heap+16#64)=.word codes := by
  have different (left right : Nat) (leftInside : left<40) (rightInside : right<40) (unequal : left≠right) :
      heap+BitVec.ofNat 64 left≠heap+BitVec.ofNat 64 right := by
    have leftNumber:=byteAddress_toNat heap left (by have h:=arena.upper; omega)
    have rightNumber:=byteAddress_toNat heap right (by have h:=arena.upper; omega)
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    change (byteAddress heap left).toNat=(byteAddress heap right).toNat at numeric
    rw [leftNumber,rightNumber] at numeric
    omega
  have zeroEight : heap≠heap+8#64 := by simpa using different 0 8 (by decide) (by decide) (by decide)
  have zeroSixteen : heap≠heap+16#64 := by simpa using different 0 16 (by decide) (by decide) (by decide)
  have eightSixteen : heap+8#64≠heap+16#64 := different 8 16 (by decide) (by decide) (by decide)
  simp [ready,written,StoreWord.put,zeroEight,zeroSixteen,eightSixteen]

/-- Exact local and global workspace/heap bindings after the real prefix. -/
theorem ready_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64) :
    (ready source heap nodes root codes).locals=source.locals ∧
    (ready source heap nodes root codes).globals.lookup (ofString "ws")=some (.val (.word heap)) ∧
    (ready source heap nodes root codes).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 40#64))) ∧
    (∀ key,key≠ofString "heap_ptr" → key≠ofString "ws" →
      (ready source heap nodes root codes).globals.lookup key=source.globals.lookup key) := by
  refine ⟨rfl,?_,?_,?_⟩
  · simp [ready,written,allocated,Input.putGlobal,HolFiniteMapExact.update,FUPDATE]
  · simp [ready,written,allocated,Input.putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "ws"≠ofString "heap_ptr" from by decide]
  · intro key notHeap notWs
    simp [ready,written,allocated,Input.putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notHeap,notWs,Ne.symm notHeap,Ne.symm notWs]

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.ready_clock
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_earlier
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_cells
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_fields
