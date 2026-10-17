import InitECandidate.Solver.Input.VarList.NormalEntry
import InitECandidate.Solver.Input.PairedScalar

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def offsetStride : ExpHOL 64 := .panop .mul [localVar "i",.const 4#64]
def offsetExpression : ExpHOL 64 := Scalar.paired32 (localVar "p") offsetStride
def recordTest : ExpHOL 64 := .cmp .notEqual (.const 0#64) (.op .or [
  .cmp .lower (localVar "o") (localVar "first"),
  .cmp .lower (localVar "len") (localVar "o"),
  .cmp .lower (localVar "o") (localVar "prev")])
def recordGuard : ProgHOL 64 := .ite recordTest (.call (some (none,none)) (ofString "ssz_fail") [.const 23#64]) .skip
def hasPrevious : ExpHOL 64 := .cmp .less (.const 0#64) (localVar "i")
def priorLengthAddress : ExpHOL 64 := .op .add [localVar "arr",
  .panop .mul [.op .sub [localVar "i",.const 1#64],.const 16#64],.const 8#64]
def priorLengthExpression : ExpHOL 64 := .op .sub [localVar "o",localVar "prev"]
def priorLengthStore : ProgHOL 64 := .ite hasPrevious (.store priorLengthAddress priorLengthExpression) .skip
def rowPointerAddress : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]
def rowPointerExpression : ExpHOL 64 := .op .add [localVar "p",localVar "o"]
def rowPointerStore : ProgHOL 64 := .store rowPointerAddress rowPointerExpression
def savePrevious : ProgHOL 64 := .assign .local (ofString "prev") (localVar "o")
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def step : ProgHOL 64 := .seq recordGuard (.seq priorLengthStore (.seq rowPointerStore (.seq savePrevious increment)))

theorem loop_body_shape : loopBody=.dec (ofString "o") .one offsetExpression step := by
  simp only [loopBody,loop,allocatedTail,firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,offsetExpression,offsetStride,Scalar.paired32,
    Scalar.pairedAddress,Scalar.shift,step,recordGuard,recordTest,priorLengthStore,hasPrevious,priorLengthAddress,
    priorLengthExpression,rowPointerStore,rowPointerAddress,rowPointerExpression,savePrevious,increment,localVar,
    List.nil_append,List.cons_append,List.append_nil]

def finalAddress : ExpHOL 64 := .op .add [localVar "arr",
  .panop .mul [.op .sub [localVar "count",.const 1#64],.const 16#64],.const 8#64]
def finalExpression : ExpHOL 64 := .op .sub [localVar "len",localVar "prev"]

theorem final_store_shape : finalLengthStore=.store finalAddress finalExpression := by
  simp only [finalLengthStore,afterLoop,allocatedTail,firstTail,body,Payload.dropLeading,Guest.guestFn_ssz_split_var_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,finalAddress,finalExpression,localVar]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.loop_body_shape
#print axioms InitECandidate.Solver.Input.VarList.final_store_shape
