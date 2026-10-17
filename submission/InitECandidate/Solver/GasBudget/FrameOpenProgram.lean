import InitECandidate.Solver.GasBudget.FrameNewCall

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev size : Nat := 104

def recordFields (parent continuation kind message : BitVec 64) : List FieldStores.Field :=
  [⟨0, .saved "parent" parent⟩, ⟨8, .globalSaved "cur_cont" continuation⟩,
   ⟨16, .saved "kind" kind⟩, ⟨40, .saved "msg" message⟩]
def activate : ProgHOL 64 :=
  .seq (.assign .global (ofString "ev") (localVar "child"))
    (.seq (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child")))
def afterClear : ProgHOL 64 := FieldStores.program "rec" "unused" (recordFields 0#64 0#64 0#64 0#64) activate
def clear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "rec", .const 104#64]
def recordProgram : ProgHOL 64 := .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 104#64] (.seq clear afterClear)
def program : ProgHOL 64 := .dec (ofString "parent") .one (.var .global (ofString "ev"))
  (.decCall (ofString "child") .one (ofString "frame_new") [localVar "msg"] recordProgram)
def body : ProgHOL 64 := match Guest.guestFn_frame_open with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = program := by
  simp only [body, program, recordProgram, clear, afterClear, activate, Guest.guestFn_frame_open,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    recordFields, FieldStores.program, FieldStores.address, FieldStores.Value.expression, localVar, addConst]

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.body_shape
