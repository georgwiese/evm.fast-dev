import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedExecution
import InitECandidate.Solver.MutableTable.MemeqSizedMapped

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def observedWord {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (offset : Nat) : BitVec 64 :=
  MemoryBytes.wordBits (source.memory (byteAddress pointer offset))

theorem observed_word {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (offset : Nat) :
    source.memory (byteAddress pointer offset) = .word (observedWord source pointer offset) := by
  cases cell : source.memory (byteAddress pointer offset) with
  | word word => simp [observedWord, MemoryBytes.wordBits, cell]

/-- Derive real aligned word mappings from a mapped byte region. -/
theorem word_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length offset : Nat)
    (aligned : pointer &&& 7#64 = 0#64) (fits : pointer.toNat + length < 2 ^ 64)
    (mapped : ∀ byte < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer byte)))
    (inside : offset + 8 ≤ length) (multiple : offset % 8 = 0) : source.memaddrs (byteAddress pointer offset) := by
  have pointerAligned : pointer.toNat % 8 = 0 := by rw [← WordBits.mask7 pointer, aligned]; rfl
  have addressNumber := byteAddress_toNat pointer offset (by omega)
  have alignEq : panByteAlignHOL (width := 64) (byteAddress pointer offset) = byteAddress pointer offset := by
    apply BitVec.eq_of_toNat_eq
    rw [InitECandidate.Solver.MutableTable.ByteStore.aligned_number, addressNumber]
    omega
  have actual := mapped offset (by omega)
  rw [alignEq] at actual
  exact actual

theorem word_inputs_of_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length : Nat)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (aAligned : a &&& 7#64 = 0#64) (bAligned : b &&& 7#64 = 0#64)
    (aFits : a.toNat + length < 2 ^ 64) (bFits : b.toNat + length < 2 ^ 64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset))) :
    WordInputs source a b length (observed source a) (observed source b) (observedWord source a) (observedWord source b) := by
  refine ⟨inputs_of_mapped source a b length aLocal bLocal lengthLocal leftMapped rightMapped, ?_, ?_, ?_, ?_⟩
  · intro offset inside multiple
    exact word_mapped source a length offset aAligned aFits leftMapped inside multiple
  · intro offset inside multiple
    exact word_mapped source b length offset bAligned bFits rightMapped inside multiple
  · intro offset _ _
    exact observed_word source a offset
  · intro offset _ _
    exact observed_word source b offset

/-- Uniform original comparison caller for the generic small widths, at
either alignment. Includes all three aligned/fallback loops and scopes.
The28/60-byte caller allowances are8/12 source clocks. -/
theorem other_call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values a b length))
    (known : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (small : length ≤ 64) (not20 : length ≠ 20) (not32 : length ≠ 32) (not52 : length ≠ 52)
    (aFits : a.toNat + length < 2 ^ 64) (bFits : b.toNat + length < 2 ^ 64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (enough : price length + 1 ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price length ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} name answer) continuation
         (output.1, restore source name output.2)) := by
  by_cases aligned : (a ||| b) &&& 7#64 = 0#64
  · have both : a &&& 7#64 = 0#64 ∧ b &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := environment source.code.lookup a b length known
    let entry := callEntryStateHOLFinite source callee
    have inputs := word_inputs_of_mapped entry a b length aLocal bLocal lengthLocal both.1 both.2 aFits bFits leftMapped rightMapped
    obtain ⟨spent, answer, spentBound, answerBound, bodyRun⟩ := aligned_other_execute entry a b length _ _ _ _ inputs small not20 not32 not52 aligned
      (by change price length ≤ source.clock - 1; omega)
    have frame : emptyLocalsHOLFinite (restore entry "i" (emptyLocalsHOLFinite {entry with clock := entry.clock - spent})) =
        emptyLocalsHOLFinite {source with clock := source.clock - 1 - spent} := rfl
    have actual := Input.CallNormal.pure_return_execute source _ name (ofString "memeq") arguments _ Memeq32.body continuation callee
      answer spent args called (by omega) bodyRun frame
    have clocks : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
    exact ⟨spent, answer, spentBound, answerBound, by simpa only [clocks] using actual⟩
  · exact unaligned_call source a b length name arguments continuation args known small aligned leftMapped rightMapped enough

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.observed_word
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.word_mapped
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.word_inputs_of_mapped
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.other_call_of_mapped
