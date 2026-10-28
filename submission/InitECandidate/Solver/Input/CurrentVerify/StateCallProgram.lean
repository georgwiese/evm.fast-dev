import InitECandidate.Solver.Input.CurrentVerify.CodeEntry
import InitECandidate.Solver.Mpt.StateInitEnvironment

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stateRootExpression : ExpHOL 64 := .load .one (.op .add [localVar "parent",.const 32#64])
def stateInitArguments : List (ExpHOL 64) := [localVar "nodedb",stateRootExpression,localVar "codedb"]
def stateInitCall : ProgHOL 64 := .call (some (none,none)) (ofString "state_init") stateInitArguments
def afterStateInit : ProgHOL 64 := match afterCodes with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- Literal current803's next call after both actual database constructors. -/
theorem state_init_shape : afterCodes=.seq stateInitCall afterStateInit := by
  simp only [afterCodes,afterNodes,nodeCall,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    stateInitCall,stateInitArguments,stateRootExpression,afterStateInit,localVar,
    CallPrefix.cut,if_neg (show ofString "check_gas_limit"≠ofString "nodedb_build" from by decide),↓reduceIte]

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.state_init_shape
