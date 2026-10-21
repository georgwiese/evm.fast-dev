import InitECandidate.Solver.Input.RunAttemptProgram
import InitECandidate.Solver.Mpt.StateInitEnvironment

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stateRootExpression : ExpHOL 64 := .load .one (.op .add [localVar "parent",.const 32#64])
def stateInitArguments : List (ExpHOL 64) := [localVar "nodedb",stateRootExpression,localVar "codedb"]
def stateInitCall : ProgHOL 64 := .call (some (none,none)) (ofString "state_init") stateInitArguments
def afterStateInit : ProgHOL 64 := match afterCodes with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- Literal original815's next call after both actual database constructors. -/
theorem state_init_shape : afterCodes=.seq stateInitCall afterStateInit := by
  simp only [afterCodes,afterNodes,constructors,afterParent,afterCount,afterHeaders,headerCall,afterPayload,body,
    Guest.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    stateInitCall,stateInitArguments,stateRootExpression,afterStateInit,localVar]

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.state_init_shape
