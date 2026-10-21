import InitECandidate.Solver.Input.RunAttemptProgram

namespace InitECandidate.Solver.Input.AttemptWrapper
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | block | header | rlp | trie | state | transaction | evm
  deriving DecidableEq

def Kind.declaration : Kind→Decl (BitVec 64)
  | .block=>Guest.guestFn_attempt_l1 | .header=>Guest.guestFn_attempt_l2 | .rlp=>Guest.guestFn_attempt_l3
  | .trie=>Guest.guestFn_attempt_l4 | .state=>Guest.guestFn_attempt_l5 | .transaction=>Guest.guestFn_attempt_l6 | .evm=>Guest.guestFn_attempt_l7

def Kind.name : Kind→MlS
  | .block=>ofString "attempt_l1" | .header=>ofString "attempt_l2" | .rlp=>ofString "attempt_l3" | .trie=>ofString "attempt_l4"
  | .state=>ofString "attempt_l5" | .transaction=>ofString "attempt_l6" | .evm=>ofString "attempt_l7"
def Kind.child : Kind→MlS
  | .block=>ofString "run_attempt" | .header=>ofString "attempt_l1" | .rlp=>ofString "attempt_l2" | .trie=>ofString "attempt_l3"
  | .state=>ofString "attempt_l4" | .transaction=>ofString "attempt_l5" | .evm=>ofString "attempt_l6"
def Kind.exception : Kind→MlS
  | .block=>ofString "BlockErr" | .header=>ofString "HdrErr" | .rlp=>ofString "RlpErr" | .trie=>ofString "MptErr"
  | .state=>ofString "StateErr" | .transaction=>ofString "TxErr" | .evm=>ofString "EvmErr"
def Kind.ordinal : Kind→Nat
  | .block=>1 | .header=>2 | .rlp=>3 | .trie=>4 | .state=>5 | .transaction=>6 | .evm=>7

def Kind.body (kind : Kind) : ProgHOL 64 := match kind.declaration with | .function fn=>progToHOL fn.body | _=>.skip

def Kind.handler (kind : Kind) : ProgHOL 64 := .seq
  (.shMemStore .op8 (.op .add [.const 2688614400#64,.const 70#64]) (localVar "e"))
  (.raise (ofString "Fail") (.const (BitVec.ofNat 64 kind.ordinal)))
def arguments : List (ExpHOL 64) := [localVar "si"]
def Kind.call (kind : Kind) : ProgHOL 64 := .call (some (none,some (kind.exception,ofString "e",kind.handler))) kind.child arguments

def formals : List (MlS×ShapeHOL) := [(ofString "si",.one)]

/-- All seven unchanged original catch layers have one literal zero
local, one real child call/handler and the original zero return. -/
theorem body_shape (kind : Kind) : kind.body=.dec (ofString "e") .one (.const 0#64) (.seq kind.call (.return (.const 0#64))) := by
  cases kind <;> simp only [Kind.body,Kind.declaration,Kind.call,Kind.handler,Kind.exception,Kind.child,Kind.ordinal,arguments,localVar,
    Guest.guestFn_attempt_l1,Guest.guestFn_attempt_l2,Guest.guestFn_attempt_l3,Guest.guestFn_attempt_l4,Guest.guestFn_attempt_l5,Guest.guestFn_attempt_l6,Guest.guestFn_attempt_l7,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (kind : Kind) (code) (installed : OriginalCode.Installed code) : code.lookup kind.name=some (formals,kind.body,.one) := by
  have selected : (functionsHOL OriginalCode.program)[815+kind.ordinal]?=some (GasBudget.OriginalCodeEnvironment.originalEntry kind.declaration) := by cases kind <;> rfl
  have checked:=OriginalCode.indexed code installed _ _ selected
  cases kind <;> simpa only [Kind.name,Kind.body,Kind.declaration,formals,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.guestFn_attempt_l1,Guest.guestFn_attempt_l2,Guest.guestFn_attempt_l3,Guest.guestFn_attempt_l4,Guest.guestFn_attempt_l5,Guest.guestFn_attempt_l6,Guest.guestFn_attempt_l7,
    paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.AttemptWrapper

#print axioms InitECandidate.Solver.Input.AttemptWrapper.body_shape
#print axioms InitECandidate.Solver.Input.AttemptWrapper.original_code
