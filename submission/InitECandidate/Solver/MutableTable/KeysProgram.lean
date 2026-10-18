import InitECandidate.Solver.MutableTable.ItemCall
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def body : ProgHOL 64 := match Guest.guestFn_htab_keys with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t", .one)]
def pairShape : ShapeHOL := .comb [.one, .one]
def pair (pointer count : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word pointer), .val (.word count)]
def outputSize : ExpHOL 64 := .op .add [.panop .mul [localVar "n", localVar "stride"], .const 8#64]
def scaled (pool index : String) : ExpHOL 64 := .op .add [localVar pool, .panop .mul [localVar index, localVar "stride"]]
def orderRead : ExpHOL 64 := .load .one (.op .add [localVar "order", .panop .mul [localVar "i", .const 8#64]])
def advance (name : String) : ProgHOL 64 := .assign .local (ofString name) (.op .add [localVar name, .const 1#64])
def copyCall : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [scaled "out" "k", scaled "keys" "slot", localVar "stride"]
def afterCopy : ProgHOL 64 := .seq (advance "k") (advance "i")
def loopBody : ProgHOL 64 := .dec (ofString "slot") .one orderRead (.seq copyCall afterCopy)
def condition : ExpHOL 64 := .cmp .less (localVar "i") (localVar "n")
def loop : ProgHOL 64 := .while condition loopBody
def afterLoop : ProgHOL 64 := .return (.rstruct [localVar "out", localVar "n"])
def afterOutputActions : List Action := [.declare "keys" (Find.tableLoad 32#64), .declare "order" (Find.tableLoad 56#64), .declare "i" (.const 0#64), .declare "k" (.const 0#64)]
def afterOutput : ProgHOL 64 := program afterOutputActions (.seq loop afterLoop)

theorem body_shape : body = .dec (ofString "stride") .one (Find.tableLoad 8#64)
    (.dec (ofString "n") .one (Find.tableLoad 24#64) (.decCall (ofString "out") .one (ofString "alloc") [outputSize] afterOutput)) := by
  simp only [body, Guest.guestFn_htab_keys, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Find.tableLoad, localVar,
    outputSize, afterOutput, program, afterOutputActions, loop, condition, loopBody, orderRead, copyCall, scaled, afterCopy, advance, afterLoop, Option.map_none]

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.body_shape
