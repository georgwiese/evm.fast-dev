import InitECandidate.Solver.Input.AttemptWrapperChain
import InitECandidate.Solver.Input.DeclarationClock

namespace InitECandidate.Solver.Input.Verify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_verify_stateless_new_payload with | .function fn=>progToHOL fn.body | _=>.skip

def handler : ProgHOL 64 := .seq (.assign .local (ofString "ok") (.const 0#64)) (.assign .global (ofString "fail_code") (localVar "e"))
def arguments : List (ExpHOL 64) := [localVar "si"]
def call : ProgHOL 64 := .call (some (none,some (ofString "Fail",ofString "e",handler))) (ofString "attempt_l7") arguments

def declared (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "e" 0#64) "ok" 1#64

def formals : List (MlS×ShapeHOL) := [(ofString "si",.one)]

theorem body_shape : body=.dec (ofString "e") .one (.const 0#64) (.dec (ofString "ok") .one (.const 1#64) (.seq call (.return (localVar "ok")))) := by
  simp only [body,Guest.guestFn_verify_stateless_new_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,call,arguments,handler,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "verify_stateless_new_payload")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 823 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_verify_stateless_new_payload) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_verify_stateless_new_payload,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem handler_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (evaluateHOLFiniteState source handler).2.clock=source.clock :=
  QuietClock.sequence source.code _ _ (QuietClock.assign source.code _ _) (QuietClock.assign_global source.code _ _) source rfl

theorem body_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source body).2.clock=(evaluateHOLFiniteState (declared source) call).2.clock := by
  rw [body_shape,ScalarScope.declare_word_clock source "e" (.const 0#64) 0#64 _ rfl,
    ScalarScope.declare_word_clock (bind source "e" 0#64) "ok" (.const 1#64) 1#64 _ rfl]
  exact QuietClock.sequence_clock (declared source) call (.return (localVar "ok"))
    (fun current=>QuietClock.returned current.code _ current rfl)

end InitECandidate.Solver.Input.Verify

#print axioms InitECandidate.Solver.Input.Verify.body_shape
#print axioms InitECandidate.Solver.Input.Verify.original_code
#print axioms InitECandidate.Solver.Input.Verify.handler_clock
#print axioms InitECandidate.Solver.Input.Verify.body_clock
