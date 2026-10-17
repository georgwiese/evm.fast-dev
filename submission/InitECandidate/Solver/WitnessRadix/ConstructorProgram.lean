import InitECandidate.Solver.WitnessRadix.BuildProgram

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match RawProgram.guestFn_nodedb_build with
  | .function fn => progToHOL fn.body | _ => .skip
def recordLoop : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def scaled (name : String) (stride : BitVec 64) : ExpHOL 64 :=
  .op .add [localVar name, .panop .mul [localVar "i", .const stride]]
def scratch : ExpHOL 64 := .var .global (ofString "mpt_hash_scratch")
def hashArguments : List (ExpHOL 64) :=
  [.load .one (scaled "slice_arr" 16#64),
   .load .one (.op .add [localVar "slice_arr", .panop .mul [localVar "i", .const 16#64], .const 8#64]), scratch]
def copyArguments : List (ExpHOL 64) := [scaled "keys" 32#64, scratch, .const 32#64]
def stores : ProgHOL 64 :=
  .seq (.store (scaled "vals" 8#64) (scaled "slice_arr" 16#64))
    (.seq (.store (scaled "order" 8#64) (localVar "i"))
      (.assign .local (ofString "i") (addConst (localVar "i") 1#64)))
def afterHash : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "memcpy") copyArguments) stores
def recordBody : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "keccak256") hashArguments) afterHash
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")

theorem loop_shape : recordLoop = .while condition recordBody := by
  simp only [recordLoop, body, BuildProgram.loops, RawProgram.guestFn_nodedb_build,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, condition, recordBody, afterHash, hashArguments, copyArguments,
    stores, scaled, scratch, localVar, addConst, Option.map_none]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.loop_shape
