import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Blocks
import InitECandidate.Solver.MutableTable.MemeqSizedProgram

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def alignedBody : ProgHOL 64 := match MemeqSized.alignedLoops with | .seq _ (.while _ body) => body | _ => .skip
def alignedBody32 : ProgHOL 64 := match MemeqSized.alignedLoops with | .seq (.while _ body) _ => body | _ => .skip
def condition32 : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") 32#64)
def alignedProgram8 : ProgHOL 64 := .seq (.while condition8 alignedBody) program
def alignedProgram : ProgHOL 64 := .seq (.while condition32 alignedBody32) alignedProgram8
def wordCheck (left right : BitVec 64) : List CompareChain.Comparison :=
  [⟨.load .one (.op .add [localVar "a", localVar "i"]), .load .one (.op .add [localVar "b", localVar "i"]), left, right⟩]

theorem aligned_body_shape (left right : BitVec 64) : alignedBody = CompareChain.prefixChecks (wordCheck left right) Memeq32.increment8 := by
  simp only [alignedBody, MemeqSized.alignedLoops, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, CompareChain.prefixChecks,
    CompareChain.returned, wordCheck, Memeq32.increment8, addConst, localVar]

theorem aligned_loops_shape : MemeqSized.alignedLoops = .seq (.while condition32 alignedBody32) (.while condition8 alignedBody) := by
  simp only [MemeqSized.alignedLoops, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, alignedBody, alignedBody32, condition32, condition8, Memeq32.condition8,
    addConst, localVar]

theorem sequence_assoc {F : Type} (source : PanSemStateFiniteExact 64 F) (first second third : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq (.seq first second) third) = evaluateHOLFiniteState source (.seq first (.seq second third)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  cases actual : evaluateHOLFiniteState source first with
  | mk result post => cases result <;> rfl

structure WordInputs {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64) : Prop where
  bytes : Inputs source a b length left right
  leftMapped : ∀ index, index + 8 ≤ length → index % 8 = 0 → source.memaddrs (a + BitVec.ofNat 64 index)
  rightMapped : ∀ index, index + 8 ≤ length → index % 8 = 0 → source.memaddrs (b + BitVec.ofNat 64 index)
  leftStored : ∀ index, index + 8 ≤ length → index % 8 = 0 → source.memory (a + BitVec.ofNat 64 index) = .word (leftWords index)
  rightStored : ∀ index, index + 8 ≤ length → index % 8 = 0 → source.memory (b + BitVec.ofNat 64 index) = .word (rightWords index)

theorem WordInputs.indexed {F : Type} {source : PanSemStateFiniteExact 64 F} {a b : BitVec 64} {length : Nat}
    {left right : Nat → UInt8} {leftWords rightWords : Nat → BitVec 64}
    (inputs : WordInputs source a b length left right leftWords rightWords) (clock index : Nat) :
    WordInputs (Memeq32.indexed source clock index) a b length left right leftWords rightWords :=
  ⟨inputs.bytes.indexed clock index, inputs.leftMapped, inputs.rightMapped, inputs.leftStored, inputs.rightStored⟩

/-- One real aligned word comparison, including mismatch return and index
advance. Its enclosing while accounts for the clock. -/
theorem aligned_block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64)
    (inputs : WordInputs source a b length left right leftWords rightWords)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index + 8 ≤ length) (multiple : index % 8 = 0) :
    evaluateHOLFiniteState source alignedBody =
      if CompareChain.agrees (wordCheck (leftWords index) (rightWords index)) then
        (none, WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 index + 8#64))
      else (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  have ready : ∀ check ∈ wordCheck (leftWords index) (rightWords index), CompareChain.Ready source check := by
    intro check member
    simp only [wordCheck, List.mem_cons, List.not_mem_nil, or_false] at member
    subst check
    constructor
    · simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, inputs.bytes.aLocal, current,
        valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL,
        inputs.leftMapped index inside multiple, inputs.leftStored index inside multiple]
    · simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, inputs.bytes.bLocal, current,
        valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL,
        inputs.rightMapped index inside multiple, inputs.rightStored index inside multiple]
  rw [aligned_body_shape (leftWords index) (rightWords index), CompareChain.execute_prefix source _ Memeq32.increment8 ready,
    Memeq32.increment8_execute source (BitVec.ofNat 64 index) current]

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_body_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_loops_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.WordInputs.indexed
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_block_execute
