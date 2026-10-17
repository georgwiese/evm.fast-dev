import InitECandidate.Solver.Input.HeaderEncoding.Frames
import InitECandidate.Solver.Input.RlpLength.TransactionPhase

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS×ShapeHOL) := [(ofString "hdr",.one),(ofString "pl",.one)]
def payloadCell (offset : BitVec 64) : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const offset])
def entryBindings : List (String×ExpHOL 64) := [
  ("total",.rfield 1 (localVar "he")),("txs",payloadCell 32#64),("ntx",payloadCell 40#64),
  ("tl",.const 0#64),("i",.const 0#64)]
def afterRelease : ProgHOL 64 := WitnessRadix.BuildEntry.declarations entryBindings transactionPhase
def afterHeader : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) afterRelease
def afterMark : ProgHOL 64 := .decCall (ofString "he") HeaderEncoding.returnShape (ofString "encode_header") [localVar "hdr"] afterHeader

theorem entry_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [afterMark,afterHeader,afterRelease,entryBindings,WitnessRadix.BuildEntry.declarations]
  rw [transactionPhase,transaction_loop_shape,transaction_suffix_shape,afterTransactionHeader,enterWithdrawals,withdrawalPhase,loop_shape,suffix_shape]
  simp only [body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    entryBindings,payloadCell,HeaderEncoding.returnShape,localVar]
  rfl

structure Codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  header : source.code.lookup (ofString "encode_header")=some (HeaderEncoding.formals,HeaderEncoding.body,HeaderEncoding.returnShape)
  headerCodes : HeaderEncoding.Codes source
  tailCodes : HeaderEncoding.TailCodes source
  alloc : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one)
  mark : source.code.lookup (ofString "heap_mark")=some ([],HeapScope.markBody,.one)
  release : source.code.lookup (ofString "heap_release")=some (HeapScope.releaseFormals,HeapScope.releaseBody,.one)
  bytesSize : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one)
  withdrawal : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one)
  wordSize : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one)

theorem Codes.of_code (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (same : target.code=source.code) (codes : Codes source) : Codes target := by
  refine ⟨?_,HeaderEncoding.Codes.of_code source target same codes.headerCodes,
    HeaderEncoding.TailCodes.of_code source target same codes.tailCodes,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [same]
  · exact codes.header
  · exact codes.alloc
  · exact codes.mark
  · exact codes.release
  · exact codes.bytesSize
  · exact codes.withdrawal
  · exact codes.wordSize

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.entry_shape
#print axioms InitECandidate.Solver.Input.RlpLength.Block.Codes.of_code
