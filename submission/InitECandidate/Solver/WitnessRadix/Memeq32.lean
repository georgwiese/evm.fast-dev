import InitECandidate.Solver.WitnessRadix.CompareChain
import InitECandidate.Solver.PanState
import Guest.Ast

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def body : ProgHOL 64 :=
  match Guest.guestFn_memeq with
  | .function fn => progToHOL fn.body
  | _ => .skip

def alignmentTest : ExpHOL 64 :=
  .cmp .equal (.op .and [.op .or [localVar "a", localVar "b"], .const 7#64]) (.const 0#64)
def sizeTest (size : BitVec 64) : ExpHOL 64 := .cmp .equal (localVar "n") (.const size)

structure Parts where
  twenty : ProgHOL 64
  thirtyTwo : ProgHOL 64
  otherAligned : ProgHOL 64
  tailCode : ProgHOL 64

def parts : Parts :=
  match body with
  | .dec _ _ _ (.seq (.ite _ (.seq (.ite _ twenty _) (.seq (.ite _ thirtyTwo _) other)) _) tailCode) =>
      ⟨twenty, thirtyTwo, other, tailCode⟩
  | _ => ⟨.skip, .skip, .skip, .skip⟩

theorem body_shape : body =
    .dec (ofString "i") .one (.const 0#64)
      (.seq (.ite alignmentTest
        (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
          (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip)
        parts.tailCode) := by
  simp only [body, parts, Guest.guestFn_memeq, alignmentTest, sizeTest, localVar,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]

def wordAt (name : String) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .load .one (localVar name)
  else .load .one (addConst (localVar name) (BitVec.ofNat 64 offset))

def checks (left right : Fin 4 → BitVec 64) : List CompareChain.Comparison :=
  [⟨wordAt "a" 0, wordAt "b" 0, left 0, right 0⟩,
   ⟨wordAt "a" 8, wordAt "b" 8, left 1, right 1⟩,
   ⟨wordAt "a" 16, wordAt "b" 16, left 2, right 2⟩,
   ⟨wordAt "a" 24, wordAt "b" 24, left 3, right 3⟩]

theorem thirtyTwo_shape (left right : Fin 4 → BitVec 64) :
    parts.thirtyTwo = CompareChain.chain (checks left right) := by
  simp only [parts, body, Guest.guestFn_memeq, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, checks, CompareChain.chain, CompareChain.returned,
    wordAt, addConst, localVar, ↓reduceIte]
  rfl

theorem eval_wordAt {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : String) (pointer value : BitVec 64) (offset : Nat)
    (argument : state.locals.lookup (ofString name) = some (.val (.word pointer)))
    (mapped : state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (word : state.memory (pointer + BitVec.ofNat 64 offset) = .word value) :
    eval state (wordAt name offset) = some (.val (.word value)) := by
  classical
  by_cases zero : offset = 0
  · subst offset
    have mapped' : state.memaddrs pointer := by simpa using mapped
    have word' : state.memory pointer = .word value := by simpa using word
    simp [eval, wordAt, localVar, evalHOLExact, toExact, argument,
      isWfShapeExactHOL, memLoadHOLExact, mapped', word']
  · simp [eval, wordAt, zero, addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, argument, isWfShapeExactHOL, memLoadHOLExact, mapped, word,
      valueIsWord, valueWord, wordOpHOL, wordOp]

/-- The exact fixed-source 32-byte fast comparison block, including every
early mismatch and the success return, for arbitrary source clocks. -/
theorem fast_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → BitVec 64)
    (ready : ∀ check ∈ checks left right, CompareChain.Ready state check) :
    evaluateHOLFiniteState state parts.thirtyTwo =
      (some (.returned (.val (.word (if CompareChain.agrees (checks left right) then 1#64 else 0#64)))),
        emptyLocalsHOLFinite state) := by
  rw [thirtyTwo_shape left right]
  exact CompareChain.execute state _ ready

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.body_shape
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.thirtyTwo_shape
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.eval_wordAt
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.fast_execute
