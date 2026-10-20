import InitECandidate.Solver.Input.Requests.SetupProgram

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def offsetName : Nat → String | 0 => "o0" | 1 => "o1" | 2 => "o2" | 3 => "o3" | _ => "o4"
def countName : Nat → String | 0 => "n0" | 1 => "n1" | 2 => "n2" | 3 => "n3" | _ => "n4"
def elementSize : Nat → BitVec 64 | 0 => 192#64 | 1 => 76#64 | 2 => 116#64 | 3 => 184#64 | _ => 68#64

def countArguments (index : Nat) : List (ExpHOL 64) := [
  .op .sub [if index + 1 < 5 then localVar (offsetName (index+1)) else localVar "len",localVar (offsetName index)],
  .const (elementSize index),.const 9223372036854775807#64]
def countStage (index : Nat) : ProgHOL 64 := Payload.dropLeading index countCalls

theorem count_stage_shape (index : Nat) (small : index < 5) : countStage index =
    .decCall (ofString (countName index)) .one (ofString "ssz_fixed_list_count") (countArguments index) (countStage (index+1)) := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;>
    simp only [countStage,countCalls,afterAllocation,afterOffsets,offsetTail,body,Guest.guestFn_decode_requests,Payload.dropLeading,progToHOL,expToHOL,
      shapeToHOL,List.map_cons,List.map_nil,Option.map_none,countArguments,countName,offsetName,elementSize,localVar]
  all_goals rfl

theorem count_names_distinct (left right : Nat) (leftSmall : left < 5) (rightSmall : right < 5) (different : left ≠ right) :
    ofString (countName left) ≠ ofString (countName right) := by
  have lc : left = 0 ∨ left = 1 ∨ left = 2 ∨ left = 3 ∨ left = 4 := by omega
  have rc : right = 0 ∨ right = 1 ∨ right = 2 ∨ right = 3 ∨ right = 4 := by omega
  rcases lc with rfl | rfl | rfl | rfl | rfl <;> rcases rc with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (different rfl) | decide

theorem element_size_nonzero (index : Nat) : elementSize index ≠ 0#64 ∧ (elementSize index).toNat ≤ 2^63 := by
  cases index with
  | zero => decide
  | succ index => cases index with
    | zero => decide
    | succ index => cases index with
      | zero => decide
      | succ index => cases index <;> simp only [elementSize] <;> decide

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.count_stage_shape
#print axioms InitECandidate.Solver.Input.Requests.count_names_distinct
#print axioms InitECandidate.Solver.Input.Requests.element_size_nonzero
