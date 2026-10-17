import InitECandidate.Solver.MutableTable.SetProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.MutableTable.Grow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_htab_grow with
  | .function fn => progToHOL fn.body | _ => .skip
def times (left right : ExpHOL 64) : ExpHOL 64 := .panop .mul [left, right]
def headerStore (offset : BitVec 64) (value : ExpHOL 64) : ProgHOL 64 := .store (.op .add [localVar "t", .const offset]) value
def indexRead : ExpHOL 64 := .load .one (.op .add [localVar "order", times (localVar "k") (.const 8#64)])
def keyAddress : ExpHOL 64 := .op .add [localVar "keys", times (localVar "i") (localVar "stride")]
def valueRead : ExpHOL 64 := .load .one (.op .add [localVar "vals", times (localVar "i") (.const 8#64)])
def insertCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_insert_raw") [localVar "t", keyAddress, valueRead]
def increment : ProgHOL 64 := .assign .local (ofString "k") (.op .add [localVar "k", .const 1#64])
def loopBody : ProgHOL 64 := .dec (ofString "i") .one indexRead (.seq insertCall increment)
def loopTest : ExpHOL 64 := .cmp .less (localVar "k") (localVar "nitems")
def loop : ProgHOL 64 := .while loopTest loopBody
def returnZero : ProgHOL 64 := .return (.const 0#64)
def afterSetup : ProgHOL 64 := .dec (ofString "k") .one (.const 0#64) (.seq loop returnZero)
def actions : List Action :=
  [.declare "cap" (Find.tableLoad 16#64), .declare "stride" (Find.tableLoad 8#64),
   .declare "keys" (Find.tableLoad 32#64), .declare "vals" (Find.tableLoad 40#64),
   .declare "order" (Find.tableLoad 56#64), .declare "nitems" (Find.tableLoad 24#64),
   .declare "ncap" (times (localVar "cap") (.const 2#64)),
   .allocate "nkeys" (times (localVar "ncap") (localVar "stride")),
   .allocate "nvals" (times (localVar "ncap") (.const 8#64)),
   .allocate "nused" (localVar "ncap"),
   .allocate "norder" (times (localVar "ncap") (.const 8#64)),
   .allocate "norder_pos" (times (localVar "ncap") (.const 8#64)),
   .command (.call (some (none, none)) (ofString "memzero") [localVar "nused", localVar "ncap"]),
   .command (headerStore 16#64 (localVar "ncap")),
   .command (headerStore 32#64 (localVar "nkeys")), .command (headerStore 40#64 (localVar "nvals")),
   .command (headerStore 48#64 (localVar "nused")), .command (headerStore 56#64 (localVar "norder")),
   .command (headerStore 64#64 (localVar "norder_pos")), .command (headerStore 24#64 (.const 0#64))]

theorem body_shape : body = program actions afterSetup := by
  simp only [body, Guest.guestFn_htab_grow, progToHOL, expToHOL, shapeToHOL, program, actions, afterSetup,
    loop, loopTest, loopBody, indexRead, insertCall, keyAddress, valueRead, increment, returnZero, headerStore, times,
    Find.tableLoad, localVar, List.map_cons, List.map_nil, Option.map_none]

end InitECandidate.Solver.MutableTable.Grow

#print axioms InitECandidate.Solver.MutableTable.Grow.body_shape
