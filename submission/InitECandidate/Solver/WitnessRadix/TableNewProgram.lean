import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def body : ProgHOL 64 := match Guest.guestFn_htab_new with
  | .function fn => progToHOL fn.body | _ => .skip
def headerStore (offset : BitVec 64) (value : ExpHOL 64) : ProgHOL 64 :=
  .store (addConst (localVar "t") offset) value
def capacityTimes (factor : ExpHOL 64) : ExpHOL 64 := .panop .mul [localVar "cap", factor]
def stride : ExpHOL 64 := .op .and
  [.op .add [localVar "key_len", .const 7#64], .op .sub [.const 0#64, .const 8#64]]
def actions : List Action :=
  [.allocate "t" (.const 72#64), .declare "stride" stride,
   .command (headerStore 0#64 (localVar "key_len")),
   .command (headerStore 8#64 (localVar "stride")),
   .command (headerStore 16#64 (localVar "cap")),
   .command (headerStore 24#64 (.const 0#64)),
   .allocate "keys" (capacityTimes (localVar "stride")),
   .command (headerStore 32#64 (localVar "keys")),
   .allocate "vals" (capacityTimes (.const 8#64)),
   .command (headerStore 40#64 (localVar "vals")),
   .allocate "used" (localVar "cap"),
   .command (.call (some (none, none)) (ofString "memzero") [localVar "used", localVar "cap"]),
   .command (headerStore 48#64 (localVar "used")),
   .allocate "order" (capacityTimes (.const 8#64)),
   .command (headerStore 56#64 (localVar "order")),
   .allocate "order_pos" (capacityTimes (.const 8#64)),
   .command (headerStore 64#64 (localVar "order_pos"))]
def returnTable : ProgHOL 64 := .return (localVar "t")

theorem body_shape : body = program actions returnTable := by
  simp only [body, Guest.guestFn_htab_new, progToHOL, expToHOL, shapeToHOL,
    actions, program, returnTable, headerStore, capacityTimes, stride, localVar, addConst,
    List.map_cons, List.map_nil, Option.map_none]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.body_shape
