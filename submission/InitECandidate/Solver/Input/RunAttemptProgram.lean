import InitECandidate.Solver.Input.MainHeaderValidatorContext

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_run_attempt with | .function fn=>progToHOL fn.body | _=>.skip
def afterPayload : ProgHOL 64 := match body with | .dec _ _ _ rest=>rest | _=>.skip
def headerCall : ProgHOL 64 := match afterPayload with | .seq _ rest=>rest | _=>.skip
def afterHeaders : ProgHOL 64 := match headerCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterCount : ProgHOL 64 := match afterHeaders with | .dec _ _ _ rest=>rest | _=>.skip
def afterParent : ProgHOL 64 := match afterCount with | .seq _ (.dec _ _ _ rest)=>rest | _=>.skip
def constructors : ProgHOL 64 := match afterParent with | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip
def afterNodes : ProgHOL 64 := match constructors with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterCodes : ProgHOL 64 := match afterNodes with | .decCall _ _ _ _ rest=>rest | _=>.skip

def field (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "si",.const (BitVec.ofNat 64 offset)])
def headerArguments : List (ExpHOL 64) := [field 72,field 80]
def nodeArguments : List (ExpHOL 64) := [field 40,field 48]
def codeArguments : List (ExpHOL 64) := [field 56,field 64]
def parentExpression : ExpHOL 64 := .load .one (.op .add [.rfield 0 (localVar "vh"),.panop .mul [.op .sub [localVar "nh",.const 1#64],.const 8#64]])
def emptyGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "nh") (.const 0#64)) (.raise (ofString "BlockErr") (.const 3#64)) .skip

def formals : List (MlS×ShapeHOL) := [(ofString "si",.one)]

set_option maxRecDepth 100000 in
/-- Projections of unchanged original run_attempt815 through its actual
validator, nonempty guard, parent read, globals and two witness constructors. -/
theorem shapes :
    body=.dec (ofString "pl") .one (field 0) afterPayload ∧
    afterPayload=.seq .skip headerCall ∧
    headerCall=.decCall (ofString "vh") Headers.Validate.resultShape (ofString "validate_headers") headerArguments afterHeaders ∧
    afterHeaders=.dec (ofString "nh") .one (field 80) afterCount ∧
    afterCount=.seq emptyGuard (.dec (ofString "parent") .one parentExpression afterParent) ∧
    afterParent=.seq (.assign .global (ofString "block_hashes") (.rfield 1 (localVar "vh")))
      (.seq (.assign .global (ofString "block_hashes_n") (localVar "nh")) (.seq .skip constructors)) ∧
    constructors=.decCall (ofString "nodedb") .one (ofString "nodedb_build") nodeArguments afterNodes ∧
    afterNodes=.decCall (ofString "codedb") .one (ofString "nodedb_build") codeArguments afterCodes := by
  simp only [body,Guest.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    afterPayload,headerCall,afterHeaders,afterCount,afterParent,constructors,afterNodes,afterCodes,field,headerArguments,nodeArguments,codeArguments,parentExpression,emptyGuard,localVar,Headers.Validate.resultShape]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "run_attempt")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 815 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_run_attempt) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_run_attempt,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.shapes
#print axioms InitECandidate.Solver.Input.RunAttempt.original_code
