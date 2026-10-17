import InitECandidate.Solver.Input.VarList.RecordGeometry
import InitECandidate.Solver.WitnessRadix.Keccak256Allocated

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- Nonempty normal decoder records expose the real aligned array allocation.
Empty lists must instead use their zero-record constructor path. -/
theorem Records.array_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length)
    (nonemptyLength : length≠0) :
    0<decodedCount input start length ∧ 2701131776≤array.toNat ∧ array.toNat%8=0 ∧
      array.toNat+16*decodedCount input start length≤33806089496 ∧
      pointer.toNat+input.length%2^64+8≤array.toNat := by
  classical
  rcases records with empty|nonempty
  · exact False.elim (nonemptyLength empty)
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have after : pointer.toNat+input.length%2^64+8≤array.toNat := by simpa only [pointerEq,arrayEq] using plan.arrayAfter
    have lower : 2701131776≤pointer.toNat := by simpa only [pointerEq] using plan.inputLower
    simp only [decodedCount,if_neg nonemptyLength]
    refine ⟨?_,by omega,?_,?_,after⟩
    · rw [←countEq];exact plan.positive
    · rw [←arrayEq];exact plan.arrayAligned
    · rw [←arrayEq,←countEq];exact plan.arrayRoom

/-- Actual pointer cells without a first-byte-read premise. In particular,
empty items need no successful read from their one-past-the-end pointer. -/
theorem Records.pointer_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length) :
    ∀ index<decodedCount input start length,
      source.memory (row (decodedArray array length) index)=.word (recordPointer input pointer start index) := by
  classical
  rcases records with empty|nonempty
  · simp [decodedCount,empty]
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have nonemptyLength : length≠0 := by have h:=plan.header;have p:=plan.positive;rw [lengthEq] at h;omega
    simp only [decodedCount,decodedArray,if_neg nonemptyLength]
    intro index inside
    have this:=(complete index (by rw [countEq];exact inside)).1
    simpa only [recordPointer,pointerEq,arrayEq,startEq] using this

/-- Decoder evidence supplies each actual hash-input arena. The fixed state,
padding and digest arenas remain startup/global-allocation obligations. -/
theorem Records.hash_buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length)
    (stp pad out : BitVec 64) (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena out 32) :
    ∀ index<decodedCount input start length,
      Keccak256.Buffers stp (recordPointer input pointer start index) pad out
        (recordLength input start length (decodedCount input start length) index).toNat := by
  intro index inside
  exact ⟨stateArena,stateAligned,(records.slice_geometry source input pointer array start length index inside).2.2.1,
    paddingArena,paddingAligned,outputArena⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.array_geometry
#print axioms InitECandidate.Solver.Input.VarList.Records.pointer_cells
#print axioms InitECandidate.Solver.Input.VarList.Records.hash_buffers
