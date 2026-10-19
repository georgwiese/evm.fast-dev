import InitECandidate.Solver.MutableTable.MemeqSizedMapped
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedMapped

namespace InitECandidate.Solver.MutableTable.MemeqSmall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem fast_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : MemeqSized.Kind) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 (MemeqSized.keySize kind)))))
    (aligned : (a ||| b) &&& 7#64 = 0#64)
    (aFits : a.toNat + MemeqSized.keySize kind < 2^64) (bFits : b.toNat + MemeqSized.keySize kind < 2^64)
    (leftMapped : ∀ offset < MemeqSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < MemeqSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset))) :
    ∃ answer post, (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source Memeq32.body = (some (.returned (.val (.word answer))), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite source := by
  classical
  have both : a &&& 7#64 = 0#64 ∧ b &&& 7#64 = 0#64 := by
    rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
    exact aligned
  have run := MemeqSized.aligned_of_data source kind a b _ _ _ _ aLocal bLocal lengthLocal aligned
    (MemeqSized.data_of_mapped source kind a both.1 aFits leftMapped)
    (MemeqSized.data_of_mapped source kind b both.2 bFits rightMapped)
  refine ⟨_, _, ?_, run, rfl⟩
  split <;> simp

/-- Every length up to64, including the20/32/52-byte special cases, uses the
original comparison. The mapped regions determine all actual reads. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (enough : MemeqByteRuntime.price length ≤ source.clock) :
    ∃ spent answer post, spent ≤ MemeqByteRuntime.price length ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source Memeq32.body = (some (.returned (.val (.word answer))), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - spent} := by
  classical
  by_cases aligned : (a ||| b) &&& 7#64 = 0#64
  · have both : a &&& 7#64 = 0#64 ∧ b &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    by_cases twenty : length = 20
    · subst length
      obtain ⟨answer, post, binary, run, fields⟩ := fast_execute source .address a b aLocal bLocal lengthLocal aligned aFits bFits leftMapped rightMapped
      exact ⟨0, answer, post, Nat.zero_le _, binary, run, by simpa only [Nat.sub_zero] using fields⟩
    by_cases thirtyTwo : length = 32
    · subst length
      let left : Fin 4 → BitVec 64 := fun index => MemoryBytes.wordBits (source.memory (a + BitVec.ofNat 64 (8 * index.val)))
      let right : Fin 4 → BitVec 64 := fun index => MemoryBytes.wordBits (source.memory (b + BitVec.ofNat 64 (8 * index.val)))
      have mappedA (index : Fin 4) : source.memaddrs (a + BitVec.ofNat 64 (8 * index.val)) :=
        MemeqByteRuntime.word_mapped source a 32 (8 * index.val) both.1 aFits leftMapped (by have bound := index.isLt; omega) (by omega)
      have mappedB (index : Fin 4) : source.memaddrs (b + BitVec.ofNat 64 (8 * index.val)) :=
        MemeqByteRuntime.word_mapped source b 32 (8 * index.val) both.2 bFits rightMapped (by have bound := index.isLt; omega) (by omega)
      have storedA (index : Fin 4) : source.memory (a + BitVec.ofNat 64 (8 * index.val)) = .word (left index) := by
        cases cell : source.memory (a + BitVec.ofNat 64 (8 * index.val)) with
        | word word => simp [left, MemoryBytes.wordBits, cell]
      have storedB (index : Fin 4) : source.memory (b + BitVec.ofNat 64 (8 * index.val)) = .word (right index) := by
        cases cell : source.memory (b + BitVec.ofNat 64 (8 * index.val)) with
        | word word => simp [right, MemoryBytes.wordBits, cell]
      have run := Memeq32.aligned_memory source a b left right aLocal bLocal lengthLocal aligned mappedA mappedB storedA storedB
      refine ⟨0, _, _, Nat.zero_le _, ?_, run, rfl⟩
      split <;> simp
    by_cases fiftyTwo : length = 52
    · subst length
      obtain ⟨answer, post, binary, run, fields⟩ := fast_execute source .storage a b aLocal bLocal lengthLocal aligned aFits bFits leftMapped rightMapped
      exact ⟨0, answer, post, Nat.zero_le _, binary, run, by simpa only [Nat.sub_zero] using fields⟩
    have inputs := MemeqByteRuntime.word_inputs_of_mapped source a b length aLocal bLocal lengthLocal both.1 both.2 aFits bFits leftMapped rightMapped
    obtain ⟨spent, answer, bound, binary, run⟩ := MemeqByteRuntime.aligned_other_execute source a b length _ _ _ _ inputs small twenty thirtyTwo fiftyTwo aligned enough
    exact ⟨spent, answer, _, bound, binary, run, rfl⟩
  · have inputs := MemeqByteRuntime.inputs_of_mapped source a b length aLocal bLocal lengthLocal leftMapped rightMapped
    obtain ⟨spent, answer, bound, binary, run⟩ := MemeqByteRuntime.unaligned_execute source a b length _ _ inputs small aligned enough
    exact ⟨spent, answer, _, bound, binary, run, rfl⟩

end InitECandidate.Solver.MutableTable.MemeqSmall

#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.fast_execute
#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.execute
