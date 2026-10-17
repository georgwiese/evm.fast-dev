import InitECandidate.Solver.WitnessRadix.Memeq32Memory
import InitECandidate.Solver.WitnessRadix.ComparePrefix

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def condition8 : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") 8#64)
def condition1 : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")
def increment8 : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") 8#64)

def byteBodies : ProgHOL 64 × ProgHOL 64 :=
  match parts.tailCode with
  | .seq (.while _ block) (.seq (.while _ tail) _) => (block, tail)
  | _ => (.skip, .skip)

theorem tail_shape : parts.tailCode =
    .seq (.while condition8 byteBodies.1)
      (.seq (.while condition1 byteBodies.2) (CompareChain.returned 1#64)) := by
  simp only [parts, body, byteBodies, Guest.guestFn_memeq, condition8, condition1,
    addConst, localVar, CompareChain.returned, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil]

def byteAt (name : String) (offset : Nat) : ExpHOL 64 :=
  .loadByte (.op .add (if offset = 0 then [localVar name, localVar "i"]
    else [localVar name, localVar "i", .const (BitVec.ofNat 64 offset)]))

def byteChecks (left right : Fin 8 → BitVec 64) : List CompareChain.Comparison :=
  [⟨byteAt "a" 0, byteAt "b" 0, left 0, right 0⟩,
   ⟨byteAt "a" 1, byteAt "b" 1, left 1, right 1⟩,
   ⟨byteAt "a" 2, byteAt "b" 2, left 2, right 2⟩,
   ⟨byteAt "a" 3, byteAt "b" 3, left 3, right 3⟩,
   ⟨byteAt "a" 4, byteAt "b" 4, left 4, right 4⟩,
   ⟨byteAt "a" 5, byteAt "b" 5, left 5, right 5⟩,
   ⟨byteAt "a" 6, byteAt "b" 6, left 6, right 6⟩,
   ⟨byteAt "a" 7, byteAt "b" 7, left 7, right 7⟩]

theorem byte_body_shape (left right : Fin 8 → BitVec 64) :
    byteBodies.1 = CompareChain.prefixChecks (byteChecks left right) increment8 := by
  simp only [byteBodies, parts, body, Guest.guestFn_memeq, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, byteChecks, CompareChain.prefixChecks,
    CompareChain.returned, byteAt, increment8, addConst, localVar]
  rfl

theorem increment8_execute {F : Type} (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (current : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState state increment8 = (none, bind state "i" (index + 8#64)) := by
  classical
  have valid : isValidValueHOLFinite state .local (ofString "i") (.val (.word (index + 8#64))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, current, shapeOfHOLExact, shapeEqHOL]
  rw [increment8, evaluateHOLFiniteState_assign]
  have expression : eval state (addConst (localVar "i") 8#64) = some (.val (.word (index + 8#64))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, current,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  simp only [eval] at expression
  rw [expression]
  simp only [← isValidValueHOLFinite_eq, valid, ↓reduceIte, setKvarHOLFinite, QueryBranch.bind]

/-- Actual byte-loop body: eight equality tests followed by the real i+=8
assignment, or an immediate mismatch return. The outer while pays one clock. -/
theorem byte_body_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (left right : Fin 8 → BitVec 64)
    (current : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (ready : ∀ check ∈ byteChecks left right, CompareChain.Ready state check) :
    evaluateHOLFiniteState state byteBodies.1 =
      if CompareChain.agrees (byteChecks left right) then (none, bind state "i" (index + 8#64))
      else (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite state) := by
  rw [byte_body_shape left right, CompareChain.execute_prefix state _ increment8 ready,
    increment8_execute state index current]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.tail_shape
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byte_body_shape
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byte_body_execute
