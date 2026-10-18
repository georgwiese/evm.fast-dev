import InitECandidate.Solver.MutableTable.SlotTailCall
import InitECandidate.Solver.MutableTable.MemoryModelBounds

namespace InitECandidate.Solver.MutableTable.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htab_item with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := ReadCall.formals "ordinal"
def indexRead : ExpHOL 64 := .load .one (.op .add [Find.tableLoad 56#64, .panop .mul [localVar "ordinal", .const 8#64]])

theorem body_shape : body = .dec (ofString "i") .one indexRead (.call none (ofString "htab_slot") [localVar "t", localVar "i"]) := by
  simp only [body, Guest.guestFn_htab_item, progToHOL, expToHOL, shapeToHOL, indexRead, Find.tableLoad, localVar, List.map_cons, List.map_nil, Option.map_none]

end InitECandidate.Solver.MutableTable.Item

#print axioms InitECandidate.Solver.MutableTable.Item.body_shape
