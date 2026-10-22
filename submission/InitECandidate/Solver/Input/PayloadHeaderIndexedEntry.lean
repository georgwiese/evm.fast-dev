import InitECandidate.Solver.Input.PayloadHeaderNormalTrieEntry
import InitECandidate.Solver.Mpt.IndexedSetup
import InitECandidate.Solver.Mpt.IndexedPrefixCost

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def indexedArguments : List (ExpHOL 64):=[PayloadHash.fieldExpression 32,PayloadHash.fieldExpression 40,localVar "txr"]
def afterTransactionTrie : ProgHOL 64:=match afterSizeGuard with | .seq _ rest=>rest | _=>.skip
def indexedCall : ProgHOL 64:=.call (some (none,none)) (ofString "build_mpt_indexed") indexedArguments

set_option maxRecDepth 100000 in
theorem indexed_call_shape : afterSizeGuard=.seq indexedCall afterTransactionTrie := by
  simp only [afterSizeGuard,afterLength,lengthCall,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    indexedCall,indexedArguments,afterTransactionTrie,PayloadHash.fieldExpression,localVar] <;>rfl

/-- Actual decoded transaction metadata and the constructed txr binding
supply every indexed-trie argument at the genuine guarded continuation. -/
theorem indexed_arguments (input : Guest.InputBlob) (origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header) :
    evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) indexedArguments=
      some (Mpt.Indexed.values (PayloadHashData.description input).transactions (BitVec.ofNat 64 (Payload.transactionCount input)) (afterOmmerHeap header)) := by
  let data:=PayloadHashData.description input
  have arrayRead:=data.field_read origin current _ _ _ prepared.image.payload prepared.layout.payload physical.inputFrame physical.domain physical.frame.payload
    (32,data.transactions) (by simp [PayloadHash.Description.cells])
  have countRead:=data.field_read origin current _ _ _ prepared.image.payload prepared.layout.payload physical.inputFrame physical.domain physical.frame.payload
    (40,BitVec.ofNat 64 data.transactionCount) (by simp [PayloadHash.Description.cells])
  simp only [eval] at arrayRead countRead
  have txr:=physical.outputs.transactions
  simp only [indexedArguments,evalListHOLFinite,evalListHOLExact,arrayRead,countRead,Mpt.Indexed.values]
  simp [evalHOLExact,toExact,localVar,txr,data,PayloadHashData.description]

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.indexed_call_shape
#print axioms InitECandidate.Solver.Input.PayloadHeader.indexed_arguments
