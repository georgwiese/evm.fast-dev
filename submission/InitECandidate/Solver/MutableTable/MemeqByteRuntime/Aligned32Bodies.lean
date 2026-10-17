import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedBodies

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def alignedWordAt (name : String) (offset : Nat) : ExpHOL 64 :=
  .load .one (.op .add (if offset = 0 then [localVar name, localVar "i"] else [localVar name, localVar "i", .const (BitVec.ofNat 64 offset)]))
def wordChecks32 (left right : Nat → BitVec 64) (index : Nat) : List CompareChain.Comparison :=
  [⟨alignedWordAt "a" 0, alignedWordAt "b" 0, left index, right index⟩,
   ⟨alignedWordAt "a" 8, alignedWordAt "b" 8, left (index + 8), right (index + 8)⟩,
   ⟨alignedWordAt "a" 16, alignedWordAt "b" 16, left (index + 16), right (index + 16)⟩,
   ⟨alignedWordAt "a" 24, alignedWordAt "b" 24, left (index + 24), right (index + 24)⟩]
def increment32 : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") 32#64)

theorem aligned_body32_shape (left right : Nat → BitVec 64) (index : Nat) :
    alignedBody32 = CompareChain.prefixChecks (wordChecks32 left right index) increment32 := by
  simp only [alignedBody32, MemeqSized.alignedLoops, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, CompareChain.prefixChecks,
    CompareChain.returned, wordChecks32, alignedWordAt, increment32, addConst, localVar, ↓reduceIte]
  rfl

theorem condition32_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length ≤ 64) (inside : index ≤ length)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source condition32 = some (.val (.word (if index + 32 ≤ length then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat = index := by change index % 2 ^ 64 = index; exact Nat.mod_eq_of_lt (by omega)
  have nNumber : (BitVec.ofNat 64 length).toNat = length := by change length % 2 ^ 64 = length; exact Nat.mod_eq_of_lt (by omega)
  have sumNumber : (BitVec.ofNat 64 index + 32#64).toNat = index + 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [iNumber]; change index + 32 < 2 ^ 64; omega), iNumber]
    rfl
  have comparison : (BitVec.ofNat 64 length < BitVec.ofNat 64 index + 32#64) ↔ length < index + 32 := by
    change (BitVec.ofNat 64 length).toNat < (BitVec.ofNat 64 index + 32#64).toNat ↔ _
    rw [nNumber, sumNumber]
  by_cases active : index + 32 ≤ length
  · have wordNotLower : ¬ BitVec.ofNat 64 length < BitVec.ofNat 64 index + 32#64 := by rw [comparison]; omega
    simp [eval, condition32,  addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordNotLower]
  · have wordLower : BitVec.ofNat 64 length < BitVec.ofNat 64 index + 32#64 := by rw [comparison]; omega
    simp [eval, condition32,  addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordLower]

theorem aligned_word_ready {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index offset : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64)
    (inputs : WordInputs source a b length left right leftWords rightWords)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index + offset + 8 ≤ length) (multiple : (index + offset) % 8 = 0) :
    CompareChain.Ready source ⟨alignedWordAt "a" offset, alignedWordAt "b" offset, leftWords (index + offset), rightWords (index + offset)⟩ := by
  have leftMap := inputs.leftMapped (index + offset) inside multiple
  have rightMap := inputs.rightMapped (index + offset) inside multiple
  have leftRead := inputs.leftStored (index + offset) inside multiple
  have rightRead := inputs.rightStored (index + offset) inside multiple
  simp only [BitVec.ofNat_add] at leftMap rightMap leftRead rightRead
  by_cases zero : offset = 0
  · subst offset
    simp only [Nat.add_zero, BitVec.add_zero] at leftMap rightMap leftRead rightRead
    constructor
    all_goals simp [eval, alignedWordAt, evalHOLExact, evalListHOLExact, toExact, localVar, inputs.bytes.aLocal, inputs.bytes.bLocal, current,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL, leftMap, rightMap, leftRead, rightRead]
  · constructor
    all_goals simp [eval, alignedWordAt, zero, evalHOLExact, evalListHOLExact, toExact, localVar, inputs.bytes.aLocal, inputs.bytes.bLocal, current,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL, leftMap, rightMap, leftRead, rightRead]

/-- Actual four-word comparison body and32-byte index advance, including
every early mismatch and preserving memory/control state. -/
theorem aligned_block32_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64)
    (inputs : WordInputs source a b length left right leftWords rightWords)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index + 32 ≤ length) (multiple : index % 8 = 0) :
    evaluateHOLFiniteState source alignedBody32 =
      if CompareChain.agrees (wordChecks32 leftWords rightWords index) then
        (none, WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 index + 32#64))
      else (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  have ready : ∀ check ∈ wordChecks32 leftWords rightWords index, CompareChain.Ready source check := by
    intro check member
    simp only [wordChecks32, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa only [Nat.add_zero] using aligned_word_ready source a b length index 0 left right leftWords rightWords inputs current (by omega) (by omega)
    · simpa only [Nat.add_zero] using aligned_word_ready source a b length index 8 left right leftWords rightWords inputs current (by omega) (by omega)
    · simpa only [Nat.add_zero] using aligned_word_ready source a b length index 16 left right leftWords rightWords inputs current (by omega) (by omega)
    · simpa only [Nat.add_zero] using aligned_word_ready source a b length index 24 left right leftWords rightWords inputs current (by omega) (by omega)
  have stepped := StateSteps.assign_execute source "i" (addConst (localVar "i") 32#64)
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 index + 32#64) current (by
      simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, current, valueIsWord, valueWord, wordOpHOL, wordOp])
  change evaluateHOLFiniteState source increment32 = _ at stepped
  rw [aligned_body32_shape leftWords rightWords index, CompareChain.execute_prefix source _ increment32 ready, stepped]

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_body32_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.condition32_read
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_word_ready
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_block32_execute
