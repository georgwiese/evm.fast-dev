import InitECandidate.Solver.Input.RequestRootHashProgram
import InitECandidate.Solver.Input.PayloadHashPrice
import InitECandidate.Solver.Input.RequestsHashMemory

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Phase where | payload | blobs | parent | requests | root

def fieldExpression (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "si",.const (BitVec.ofNat 64 offset)])
def outputExpression (slot : Nat) : ExpHOL 64 := if slot=0 then localVar "ch" else .op .add [localVar "ch",.const (BitVec.ofNat 64 (32*slot))]
def Phase.function : Phase→MlS
  | .payload=>ofString "htr_payload" | .blobs=>ofString "htr_plist_chunks" | .parent=>ofString "memcpy"
  | .requests=>ofString "htr_requests" | .root=>ofString "merkleize"
def Phase.arguments : Phase→List (ExpHOL 64)
  | .payload=>[fieldExpression 0,localVar "ch"]
  | .blobs=>[fieldExpression 8,fieldExpression 16,fieldExpression 16,outputExpression 1]
  | .parent=>[outputExpression 2,fieldExpression 24,.const 32#64]
  | .requests=>[fieldExpression 32,outputExpression 3]
  | .root=>[localVar "ch",.const 4#64,.const 4#64,localVar "out"]
def Phase.call (phase : Phase) : ProgHOL 64 := .call (some (none,none)) phase.function phase.arguments
def phases : List Phase := [.payload,.blobs,.parent,.requests,.root]
def pipeline (phases : List Phase) : ProgHOL 64 := phases.foldr (fun phase tail=>.seq phase.call tail) FixedHash.releaseSuffix
def afterMark : ProgHOL 64 := .decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 4#64,.const 32#64]] (pipeline phases)

set_option maxRecDepth 100000 in
/-- Literal original request-root hash phases and outer scopes. These are
proof reifications kernel matched to function203, with every call retained. -/
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,afterMark,pipeline,phases,List.foldr_cons,List.foldr_nil,Phase.call,Phase.function,Phase.arguments,
    outputExpression,fieldExpression,FixedHash.releaseSuffix,Guest.guestFn_htr_new_payload_request,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,localVar]
  rfl

theorem phase_local (phase : Phase) (key : MlS) : LocalPrefix key phase.call := .call none _ _ (by intro name impossible; cases impossible)

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.body_shape
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_local
