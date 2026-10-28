import Guest.SoftwareAst
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.DeclarationPrefixCost
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.CurrentKeccak.Permutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_keccak_f1600 with | .function fn=>progToHOL fn.body | _=>.skip
def afterLanes : ProgHOL 64 := ClockCost.dropDeclarations 25 body
def roundBody : ProgHOL 64 := match afterLanes with | .dec _ _ _ (.seq (.while _ step) _)=>step | _=>.skip
def storeTail : ProgHOL 64 := match afterLanes with | .dec _ _ _ (.seq _ tail)=>tail | _=>.skip
def condition : ExpHOL 64 := .cmp .less (localVar "r") (.const 24#64)
def formals : List (MlS×ShapeHOL) := [(ofString "stp",.one)]

set_option maxRecDepth 100000 in
theorem after_lanes_shape : afterLanes=.dec (ofString "r") .one (.const 0#64) (.seq (.while condition roundBody) storeTail) := by
  simp only [afterLanes,roundBody,storeTail,condition,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "keccak_f1600")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 90 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_keccak_f1600) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_keccak_f1600,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.CurrentKeccak.Permutation

#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.after_lanes_shape
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.original_code
