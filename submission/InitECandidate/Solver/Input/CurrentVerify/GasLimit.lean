import InitECandidate.Solver.Input.UDivMod.CurrentCost
import InitECandidate.Solver.Input.PureDecision

namespace InitECandidate.Solver.Input.CurrentVerify.GasLimit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_check_gas_limit with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "gas_limit",.one),(ofString "parent_gas_limit",.one)]
def tail : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "max_delta") .one (ofString "udiv") [localVar "parent_gas_limit",.const 1024#64] tail := by
  simp only [body,tail,Guest.Software.guestFn_check_gas_limit,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "check_gas_limit")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 216 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_check_gas_limit) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_check_gas_limit,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem tail_decision : PureDecision tail := by
  simp only [tail,body,Guest.Software.guestFn_check_gas_limit,progToHOL]
  exact .seq (.ite _ (.returned _) .skip) (.seq (.ite _ (.returned _) .skip) (.seq (.ite _ (.returned _) .skip) (.returned _)))

/-- The actual gas-limit check has only the current64-round unsigned
software division and two call ticks. Invalid arguments and short clocks
are included; no successful check is assumed. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body 66 := by
  intro source same
  rw [body_shape]
  apply ClockCost.word_pair_const source (ofString "udiv") (ofString "a") (ofString "b") (ofString "max_delta") UDivMod.Divide.body tail .one .one
    (localVar "parent_gas_limit") 1024#64 65 0 (by decide)
    (UDivMod.Divide.original_code source.code (by rw [same]; exact installed))
  · intro entry left codeEq aCell bCell
    exact UDivMod.Divide.nonzero_cost entry left 1024#64 aCell bCell (by decide)
      (UDivMod.original_code entry.code (by rw [codeEq,same]; exact installed))
  · exact ClockCost.of_quiet source.code tail (tail_decision.quiet source.code)

end InitECandidate.Solver.Input.CurrentVerify.GasLimit

#print axioms InitECandidate.Solver.Input.CurrentVerify.GasLimit.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.GasLimit.body_cost
