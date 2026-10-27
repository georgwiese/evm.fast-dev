import Guest.SoftwareAst
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.HostPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

namespace Byte
def body : ProgHOL 64 := match Guest.Software.guestFn_host_input_byte with
  | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "i", .one)]
def address : ExpHOL 64 := .op .add [.const 1073741840#64,
  .op .and [localVar "i", .op .sub [.const 0#64, .const 8#64]]]
def load : ProgHOL 64 := .shMemLoad .opW .local (ofString "w") address
def value : ExpHOL 64 := .op .and [
  .shift .lsr (localVar "w") (.panop .mul [.op .and [localVar "i", .const 7#64], .const 8#64]),
  .const 255#64]
def tail : ProgHOL 64 := .seq load (.return value)

theorem body_shape : body = .dec (ofString "w") .one (.const 0#64) tail := by
  simp only [body, Guest.Software.guestFn_host_input_byte, progToHOL, expToHOL, shapeToHOL,
    tail, load, address, value, localVar, List.map_cons, List.map_nil, Option.map_none]
end Byte

namespace Le32
def body : ProgHOL 64 := match Guest.Software.guestFn_host_input_le32 with
  | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "i", .one)]
def value : ExpHOL 64 := .op .or [localVar "b0",
  .shift .lsl (localVar "b1") (.const 8#64),
  .shift .lsl (localVar "b2") (.const 16#64),
  .shift .lsl (localVar "b3") (.const 24#64)]
def afterB2 : ProgHOL 64 := .decCall (ofString "b3") .one (ofString "host_input_byte")
  [addConst (localVar "i") 3#64] (.return value)
def afterB1 : ProgHOL 64 := .decCall (ofString "b2") .one (ofString "host_input_byte")
  [addConst (localVar "i") 2#64] afterB2
def afterB0 : ProgHOL 64 := .decCall (ofString "b1") .one (ofString "host_input_byte")
  [addConst (localVar "i") 1#64] afterB1

theorem body_shape : body = .decCall (ofString "b0") .one (ofString "host_input_byte")
    [localVar "i"] afterB0 := by
  simp only [body, Guest.Software.guestFn_host_input_le32, progToHOL, expToHOL, shapeToHOL,
    afterB0, afterB1, afterB2, value, localVar, addConst,
    List.map_cons, List.map_nil, Option.map_none]
end Le32

end InitECandidate.Solver.Input.HostPrecheck

#print axioms InitECandidate.Solver.Input.HostPrecheck.Byte.body_shape
#print axioms InitECandidate.Solver.Input.HostPrecheck.Le32.body_shape
