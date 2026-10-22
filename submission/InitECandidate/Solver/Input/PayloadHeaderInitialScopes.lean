import InitECandidate.Solver.Input.PayloadHeaderEntryData
import InitECandidate.Solver.Input.CallPrefixDeclaration

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def afterReads : List CallPrefix.Action:=actions.drop 2
def readEntry (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  QueryBranch.bind (QueryBranch.bind source "pl" (PayloadPrefix.cursor input)) "raw" (inputPointer+62#64)

set_option maxRecDepth 100000 in
theorem initial_actions : actions=
    .declare (ofString "pl") .one (RequestRootHash.fieldExpression 0)::
    .declare (ofString "raw") .one (PayloadHash.fieldExpression 0)::afterReads := by
  simp only [actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterReads,
    List.drop_cons,List.drop_zero,RequestRootHash.fieldExpression,PayloadHash.fieldExpression,localVar]
  rfl

/-- The reached original prefix itself supplies both real local scopes;
the payload/raw words come from main's original decoder provenance. -/
theorem initial_scopes (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    CallPrefix.Execution (readEntry input source) afterReads current := by
  rw [initial_actions] at execution
  have payload:=execution.declare_next (.val (.word (PayloadPrefix.cursor input)))
    (ready.payload_read input origin initializer source root workspace nodes stateRoot codes counts prepared)
  exact payload.declare_next (.val (.word (inputPointer+62#64)))
    (ready.raw_read input origin initializer source root workspace nodes stateRoot codes counts prepared)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.initial_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.initial_scopes
