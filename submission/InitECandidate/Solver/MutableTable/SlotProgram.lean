import InitECandidate.Solver.MutableTable.MemoryModelReads
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.MutableTable.Slot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htab_slot with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t", .one), (ofString "i", .one)]
def tripleShape : ShapeHOL := .comb [.one, .one, .one]
def triple (used key value : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word used), .val (.word key), .val (.word value)]
def usedExpression : ExpHOL 64 := .loadByte (.op .add [Find.tableLoad 48#64, localVar "i"])
def keyExpression : ExpHOL 64 := .op .add [Find.tableLoad 32#64, .panop .mul [localVar "i", Find.tableLoad 8#64]]
def valueExpression : ExpHOL 64 := .load .one (.op .add [Find.tableLoad 40#64, .panop .mul [localVar "i", .const 8#64]])
def afterValue : ProgHOL 64 := .return (.rstruct [localVar "used", localVar "keyp", localVar "val"])

theorem body_shape : body = .dec (ofString "used") .one usedExpression
    (.dec (ofString "keyp") .one keyExpression (.dec (ofString "val") .one valueExpression afterValue)) := by
  simp only [body, Guest.guestFn_htab_slot, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    usedExpression, keyExpression, valueExpression, afterValue, Find.tableLoad, localVar]

end InitECandidate.Solver.MutableTable.Slot

#print axioms InitECandidate.Solver.MutableTable.Slot.body_shape
