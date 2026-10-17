import InitECandidate.Solver.Input.PayloadPrefixProgram
import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ssz_split_var_list with
  | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "len",.one),(ofString "lim",.one)]
def emptyTest : ExpHOL 64 := .cmp .equal (localVar "len") (.const 0#64)
def emptyReturn : ProgHOL 64 := .return (.rstruct [.const 0#64,.const 0#64])
def emptyGuard : ProgHOL 64 := .ite emptyTest emptyReturn .skip
def shortTest : ExpHOL 64 := .cmp .lower (localVar "len") (.const 4#64)
def shortGuard : ProgHOL 64 := .ite shortTest (.call (some (none,none)) (ofString "ssz_fail") [.const 20#64]) .skip
def firstExpression : ExpHOL 64 := Scalar.flat32 (localVar "p") []
def firstTail : ProgHOL 64 := Payload.dropLeading 3 body

theorem entry_shape : body=.seq emptyGuard (.seq shortGuard (.dec (ofString "first") .one firstExpression firstTail)) := by
  simp only [body,firstTail,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,emptyGuard,emptyTest,emptyReturn,shortGuard,shortTest,firstExpression,
    Scalar.flat32,Scalar.flatAddress,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]

def firstTest : ExpHOL 64 := .cmp .notEqual (.const 0#64) (.op .or [
  .cmp .equal (localVar "first") (.const 0#64),
  .cmp .notEqual (.op .and [localVar "first",.const 3#64]) (.const 0#64),
  .cmp .lower (localVar "len") (localVar "first")])
def firstGuard : ProgHOL 64 := .ite firstTest (.call (some (none,none)) (ofString "ssz_fail") [.const 21#64]) .skip
def countExpression : ExpHOL 64 := .shift .lsr (localVar "first") (.const 2#64)
def countTest : ExpHOL 64 := .cmp .lower (localVar "lim") (localVar "count")
def countGuard : ProgHOL 64 := .ite countTest (.call (some (none,none)) (ofString "ssz_fail") [.const 22#64]) .skip
def allocationExpression : ExpHOL 64 := .panop .mul [localVar "count",.const 16#64]
def allocatedTail : ProgHOL 64 := Payload.dropLeading 4 firstTail

theorem first_tail_shape : firstTail=.seq firstGuard (.dec (ofString "count") .one countExpression
    (.seq countGuard (.decCall (ofString "arr") .one (ofString "alloc") [allocationExpression] allocatedTail))) := by
  simp only [firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,firstGuard,firstTest,countExpression,countTest,countGuard,
    allocationExpression,allocatedTail,localVar]

def loop : ProgHOL 64 := match allocatedTail with | .dec _ _ _ (.dec _ _ _ (.seq code _))=>code | _=>.skip
def loopBody : ProgHOL 64 := match loop with | .while _ code=>code | _=>.skip
def afterLoop : ProgHOL 64 := match allocatedTail with | .dec _ _ _ (.dec _ _ _ (.seq _ rest))=>rest | _=>.skip
def loopTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "count")
def finalLengthStore : ProgHOL 64 := match afterLoop with | .seq code _=>code | _=>.skip
def returnArray : ProgHOL 64 := .return (.rstruct [localVar "arr",localVar "count"])

theorem allocated_tail_shape : allocatedTail=.dec (ofString "i") .one (.const 0#64)
    (.dec (ofString "prev") .one (localVar "first") (.seq loop afterLoop)) := by
  simp only [allocatedTail,firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,loop,afterLoop,localVar]

theorem loop_shape : loop=.while loopTest loopBody := by
  simp only [loop,allocatedTail,firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,loopTest,loopBody,localVar]

theorem after_loop_shape : afterLoop=.seq finalLengthStore returnArray := by
  simp only [afterLoop,allocatedTail,firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,finalLengthStore,returnArray,localVar]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.entry_shape
#print axioms InitECandidate.Solver.Input.VarList.first_tail_shape
#print axioms InitECandidate.Solver.Input.VarList.allocated_tail_shape
#print axioms InitECandidate.Solver.Input.VarList.loop_shape
#print axioms InitECandidate.Solver.Input.VarList.after_loop_shape
