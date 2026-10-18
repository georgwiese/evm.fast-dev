import InitECandidate.Solver.WitnessRadix.CopyWordState

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

theorem word_bits_wrap (value : HolWordLab 64) : HolWordLab.word (MemoryBytes.wordBits value) = value := by
  cases value <;> rfl

/-- Actual original word-copy stores reproduce the snapshot at every listed
destination. Source/destination separation prevents earlier writes from
changing later reads; destination injectivity prevents unrelated overwrites. -/
theorem memory_many_at (input snapshot : WordWrites.Memory) (src dst index : BitVec 64) (offsets : List Nat)
    (sourceKept : ∀ offset ∈ offsets, input (src + index + BitVec.ofNat 64 offset) = snapshot (src + index + BitVec.ofNat 64 offset))
    (apart : ∀ first ∈ offsets, ∀ second ∈ offsets, src + index + BitVec.ofNat 64 first ≠ dst + index + BitVec.ofNat 64 second)
    (injective : ∀ first ∈ offsets, ∀ second ∈ offsets, dst + index + BitVec.ofNat 64 first = dst + index + BitVec.ofNat 64 second → first = second)
    (query : Nat) (member : query ∈ offsets) :
    CopyWords.memoryMany input src dst index offsets (dst + index + BitVec.ofNat 64 query) = snapshot (src + index + BitVec.ofNat 64 query) := by
  induction offsets generalizing input with
  | nil => simp at member
  | cons head rest ih =>
    have kept (offset : Nat) (belongs : offset ∈ rest) :
        CopyWords.copyMemory input src dst index head (src + index + BitVec.ofNat 64 offset) = snapshot (src + index + BitVec.ofNat 64 offset) := by
      simp only [CopyWords.copyMemory, StoreWord.put, if_neg (apart offset (List.mem_cons_of_mem _ belongs) head (by simp))]
      exact sourceKept offset (List.mem_cons_of_mem _ belongs)
    by_cases tailMember : query ∈ rest
    · rw [CopyWords.memoryMany]
      exact ih _ kept
        (by intro first firstMember second secondMember; exact apart first (List.mem_cons_of_mem _ firstMember) second (List.mem_cons_of_mem _ secondMember))
        (by intro first firstMember second secondMember; exact injective first (List.mem_cons_of_mem _ firstMember) second (List.mem_cons_of_mem _ secondMember)) tailMember
    · have atHead : query = head := by simpa only [List.mem_cons, tailMember, or_false] using member
      subst head
      rw [CopyWords.memoryMany, CopyWords.memoryMany_away]
      · simp only [CopyWords.copyMemory, StoreWord.put, ↓reduceIte, sourceKept query member, word_bits_wrap]
      · intro offset belongs same
        have equal := injective query member offset (List.mem_cons_of_mem _ belongs) same
        exact tailMember (equal ▸ belongs)

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.word_bits_wrap
#print axioms InitECandidate.Solver.MutableTable.CopyContents.memory_many_at
