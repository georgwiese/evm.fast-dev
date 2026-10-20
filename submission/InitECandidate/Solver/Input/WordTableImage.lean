import InitECandidate.Solver.Input.WordTableFields

namespace InitECandidate.Solver.Input.InitializerWords
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The exact stored value of each real table word, including the first word,
without expanding any unrelated literal table stores. -/
theorem written_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64))
    (fits : pointer.toNat + offset + 8 * words.length < 2 ^ 64) (index : Fin words.length) :
    (written source pointer offset words).memory (byteAddress pointer (offset + 8 * index.val)) = .word (words[index.val]) := by
  induction words generalizing source offset with
  | nil => exact Fin.elim0 index
  | cons word rest ih =>
    cases index with
    | mk index inside =>
      cases index with
      | zero =>
        have absent : byteAddress pointer offset ∉ (writes pointer (offset + 8) rest).map Prod.fst := by
          intro member
          obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp member
          obtain ⟨position,lower,upper,address⟩ := writes_inside pointer (offset + 8) rest entry entryMember
          have firstNumber := byteAddress_toNat pointer offset (by simp only [List.length_cons] at fits; omega)
          have laterNumber := byteAddress_toNat pointer position (by simp only [List.length_cons] at fits; omega)
          have same : byteAddress pointer offset = byteAddress pointer position := equal.symm.trans address
          have numbers := congrArg BitVec.toNat same
          rw [firstNumber,laterNumber] at numbers
          omega
        change WordWrites.write (StoreWord.put source.memory (pointer + BitVec.ofNat 64 offset) word) (writes pointer (offset + 8) rest)
          (byteAddress pointer (offset + 8 * 0)) = .word word
        simp only [Nat.mul_zero,Nat.add_zero]
        rw [WordWrites.write_away _ _ _ absent]
        simp [StoreWord.put,byteAddress]
      | succ index =>
        let middle := {source with memory := StoreWord.put source.memory (pointer + BitVec.ofNat 64 offset) word}
        have result := ih middle (offset + 8) (by simp only [List.length_cons] at fits; omega) ⟨index,by simp only [List.length_cons] at inside; omega⟩
        have address : offset + 8 * (index + 1) = offset + 8 + 8 * index := by omega
        simpa only [written,writes,WordWrites.write,middle,address,List.getElem_cons_succ] using result

end InitECandidate.Solver.Input.InitializerWords

namespace InitECandidate.Solver.Input.WordTableInitialization
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem template_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64))
    (fits : cursor + 8 * words.length < 2 ^ 64) (index : Fin words.length) :
    (template source cursor action words).memory (byteAddress (BitVec.ofNat 64 cursor) (8 * index.val)) = .word (words[index.val]) := by
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have actual := InitializerWords.written_at (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) 0 words
    (by rw [number]; omega) index
  simpa only [Nat.zero_add,template] using actual

end InitECandidate.Solver.Input.WordTableInitialization

#print axioms InitECandidate.Solver.Input.InitializerWords.written_at
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_at
