import InitECandidate.Solver.MutableTable.ByteStore
import InitECandidate.Solver.MutableTable.MemeqSizedCall
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Call

namespace InitECandidate.Solver.MutableTable.MemeqSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def wordsOf {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (index : Fin 6) : BitVec 64 :=
  MemoryBytes.wordBits (source.memory (pointer + BitVec.ofNat 64 (8 * index.val)))
def trailingOf {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) (index : Fin 4) : UInt8 :=
  MemeqByteRuntime.observed source pointer (8 * wordCount kind + index.val)

theorem word_inside (kind : Kind) (index : Fin 6) (inside : index.val < wordCount kind) :
    8 * index.val < keySize kind := by
  cases kind <;> dsimp [wordCount, keySize, HashSized.wordCount, HashSized.keySize] at inside ⊢ <;> omega

theorem tail_inside (kind : Kind) (index : Fin 4) : 8 * wordCount kind + index.val < keySize kind := by
  have bound := index.isLt
  cases kind <;> dsimp [wordCount, keySize, HashSized.wordCount, HashSized.keySize] <;> omega

/-- Derive every fast word/tail-byte read from a mapped byte region. -/
theorem data_of_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64)
    (aligned : pointer &&& 7#64 = 0#64) (fits : pointer.toNat + keySize kind < 2 ^ 64)
    (mapped : ∀ offset < keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    Data source kind pointer (wordsOf source pointer) (trailingOf source kind pointer) := by
  have pointerAligned : pointer.toNat % 8 = 0 := by rw [← WordBits.mask7 pointer, aligned]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro index inside
    have offsetInside := word_inside kind index inside
    have addressNumber := byteAddress_toNat pointer (8 * index.val) (by omega)
    have alignEq : panByteAlignHOL (width := 64) (byteAddress pointer (8 * index.val)) = byteAddress pointer (8 * index.val) := by
      apply BitVec.eq_of_toNat_eq
      rw [InitECandidate.Solver.MutableTable.ByteStore.aligned_number, addressNumber]
      omega
    have read := mapped (8 * index.val) offsetInside
    rw [alignEq] at read
    exact read
  · intro index inside
    cases cell : source.memory (pointer + BitVec.ofNat 64 (8 * index.val)) with
    | word word => simp [wordsOf, MemoryBytes.wordBits, cell]
  · intro index
    exact MemeqByteRuntime.observed_read source pointer (8 * wordCount kind + index.val) (mapped _ (tail_inside kind index))

/-- Complete actual20/52-byte comparison caller for either alignment. All
input reads are derived from mapped regions; arbitrary contents are allowed.
The return is0or1, memory/FFI/globals are unchanged, and the caller allowance is
at most7or11source clocks respectively. This omits straight-line target work. -/
theorem call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (a b : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind a b))
    (known : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (aFits : a.toNat + keySize kind < 2 ^ 64) (bFits : b.toNat + keySize kind < 2 ^ 64)
    (leftMapped : ∀ offset < keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (enough : MemeqByteRuntime.price (keySize kind) + 1 ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ MemeqByteRuntime.price (keySize kind) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} name answer) continuation
         (output.1, restore source name output.2)) := by
  by_cases aligned : (a ||| b) &&& 7#64 = 0#64
  · have both : a &&& 7#64 = 0#64 ∧ b &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    let left := wordsOf source a
    let right := wordsOf source b
    let leftBytes := trailingOf source kind a
    let rightBytes := trailingOf source kind b
    let answer : BitVec 64 := if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64
    have answerBound : answer = 0#64 ∨ answer = 1#64 := by dsimp [answer]; split <;> simp
    have run := aligned_call source kind a b left right leftBytes rightBytes name arguments continuation args known aligned
      (data_of_mapped source kind a both.1 aFits leftMapped) (data_of_mapped source kind b both.2 bFits rightMapped) (by omega)
    exact ⟨0, answer, Nat.zero_le _, answerBound, run⟩
  · exact MemeqByteRuntime.unaligned_call source a b (keySize kind) name arguments continuation args known
      (by cases kind <;> decide) aligned leftMapped rightMapped enough

end InitECandidate.Solver.MutableTable.MemeqSized

#print axioms InitECandidate.Solver.MutableTable.MemeqSized.word_inside
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.tail_inside
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.data_of_mapped
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.call_of_mapped
