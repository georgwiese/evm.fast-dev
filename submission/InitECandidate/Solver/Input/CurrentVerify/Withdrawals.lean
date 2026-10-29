import InitECandidate.Solver.Input.CurrentVerify.IndexedTransactions
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.Input.ClockCostAssignedCurrent

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry

def countExpression : ExpHOL 64:=payloadField 56
def arrayArguments : List (ExpHOL 64):=[.op .add [.panop .mul [localVar "nwd",.const 16#64],.const 16#64]]
def arrayCall : ProgHOL 64:=.call (some (some (.global,ofString "wd_rlp_slices"),none)) (ofString "alloc") arrayArguments
def afterCount : ProgHOL 64:=match afterTransactionTrie with | .dec _ _ _ rest=>rest | _=>.skip
def afterArray : ProgHOL 64:=match afterCount with | .seq _ rest=>rest | _=>.skip
def loopAndAfter : ProgHOL 64:=match afterArray with | .dec _ _ _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .less (localVar "i") (localVar "nwd")
def loopBody : ProgHOL 64:=match loopAndAfter with | .seq (.while _ body) _=>body | _=>.skip
def afterLoop : ProgHOL 64:=match loopAndAfter with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem prefix_shapes : afterTransactionTrie=.dec (ofString "nwd") .one countExpression afterCount ∧
    afterCount=.seq arrayCall afterArray ∧ afterArray=.dec (ofString "i") .one (.const 0#64) loopAndAfter ∧
    loopAndAfter=.seq (.while test loopBody) afterLoop := by
  simp only [afterTransactionTrie,afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterCount,arrayCall,arrayArguments,afterArray,loopAndAfter,loopBody,afterLoop,test,countExpression,payloadField,Scalar.plus,localVar]
  trivial

/-- Every real encoded withdrawal owns its actual 44-byte input record,
and all records lie before the decoded-input boundary. These facts come
from the same earlier payload decoder and never assume a writer return. -/
theorem withdrawal_records {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    source.memory (record+48#64)=.word (pointer+BitVec.ofNat 64 (withdrawalStart input)) ∧
      source.memory (record+56#64)=.word (BitVec.ofNat 64 (Payload.withdrawalCount input)) ∧
      ∀ index<Payload.withdrawalCount input,
        AllocatedBytes.Arena (pointer+BitVec.ofNat 64 (withdrawalStart input+44*index)) 44 ∧
        (pointer+BitVec.ofNat 64 (withdrawalStart input+44*index)).toNat+44≤boundary := by
  obtain ⟨array,start,size,block⟩:=data.block_inputs
  refine ⟨block.data.withdrawals,block.data.nwd,?_⟩
  intro index inside
  have endBound:=block.data.inside
  have inputBefore:=block.inputBefore
  have inputLower:=data.copied.lower
  have arena : AllocatedBytes.Arena pointer (input.length%2^64):=⟨by omega,by have upper:=data.recordArena.upper; have before:=data.copied.beforeRecord; omega⟩
  have extent : withdrawalStart input+44*index+44≤input.length%2^64:=by omega
  have row:=arena.subrange pointer (input.length%2^64) (withdrawalStart input+44*index) 44 extent
  have number:=byteAddress_toNat pointer (withdrawalStart input+44*index) (by have upper:=arena.upper; omega)
  exact ⟨row,by change (pointer+BitVec.ofNat 64 (withdrawalStart input+44*index)).toNat=pointer.toNat+(withdrawalStart input+44*index) at number; omega⟩

/-- The unchanged count declaration reads the actual accepted payload
count, before allocating any withdrawal array or encoding a row. -/
theorem count_read {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) :
    eval current countExpression=some (.val (.word (BitVec.ofNat 64 (Payload.withdrawalCount input)))) := by
  have recordRead:=local_word_read current "pl" record physical.frame.payload
  exact Witness.load_word_read current (Scalar.plus (localVar "pl") 56) (record+56#64) (BitVec.ofNat 64 (Payload.withdrawalCount input))
    (Scalar.plus_read current (localVar "pl") record 56 recordRead)
    (AllocatedBytes.word_mapped current record 136 56 physical.data.arena.domain physical.data.recordArena (by decide) physical.data.recordAligned (by decide))
    (withdrawal_records physical.data).2.1

/-- The actual global-result array allocation has its own two-tick
allowance on every outcome, including its checked capacity rejection. -/
theorem array_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (countCell : source.locals.lookup (ofString "nwd")=some (.val (.word count))) :
    source.clock-(evaluateHOLFiniteState source arrayCall).2.clock≤2 := by
  let amount:=count*16#64+16#64
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arrayArguments=some (PersistentAlloc.values amount):=by
    simp [arrayArguments,PersistentAlloc.values,amount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,countCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  obtain ⟨callee,called,n⟩:=PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code installed)
  exact ClockCost.assigned_current source (some (.global,ofString "wd_rlp_slices")) (ofString "alloc") arrayArguments _ PersistentAlloc.body callee .one 1 args called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)

/-- The actual global-result array allocation supplies its own checked
room, exact heap/global update and owned row-storage extent. No initial
binding of wd_rlp_slices or later successful encoder is required. -/
theorem array_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (header heap : BitVec 64) (count : Nat)
    (frontier : HeapFrontier source header heap) (small : count≤335544) (installed : OriginalCode.Installed source.code)
    (countCell : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))))
    (normal : evaluateHOLFiniteState source arrayCall=(none,target)) :
    AllocatedBytes.Arena heap (16*count+16) ∧ 1≤source.clock ∧
      target=putGlobal (PersistentAlloc.post {source with clock:=source.clock-1} heap (BitVec.ofNat 64 (16*count+16))) "wd_rlp_slices" heap := by
  let amount:=BitVec.ofNat 64 (16*count+16)
  have amountNumber : amount.toNat=16*count+16:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arrayArguments=some (PersistentAlloc.values amount):=by
    simp [arrayArguments,PersistentAlloc.values,amount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,countCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_add,BitVec.ofNat_mul,Nat.mul_comm]
  have noWrap : heap.toNat+amount.toNat+7<2^64:=by rw [amountNumber]; have upper:=frontier.bounded; omega
  obtain ⟨room,funded,same⟩:=PersistentAlloc.global_call_normal_no_wrap source target "wd_rlp_slices" heap amount arrayArguments args installed frontier.cell noWrap normal
  exact ⟨⟨frontier.arena.lower,by rw [amountNumber] at room; omega⟩,funded,same⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.prefix_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.withdrawal_records
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.count_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.array_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.array_normal
