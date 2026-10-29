import InitECandidate.Solver.Input.CurrentVerify.IndexedTransactions
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.Input.ClockCostAssignedCurrent
import InitECandidate.Solver.Input.CurrentRlp.Withdrawal
import InitECandidate.Solver.Input.CurrentVerify.DataGlobals
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.ClockCostCurrentLoop

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
    AllocatedBytes.Arena heap (16*count+16) ∧ heap.toNat+16*count+16≤2952790016 ∧ 1≤source.clock ∧
      target=putGlobal (PersistentAlloc.post {source with clock:=source.clock-1} heap (BitVec.ofNat 64 (16*count+16))) "wd_rlp_slices" heap := by
  let amount:=BitVec.ofNat 64 (16*count+16)
  have amountNumber : amount.toNat=16*count+16:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arrayArguments=some (PersistentAlloc.values amount):=by
    simp [arrayArguments,PersistentAlloc.values,amount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,countCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_add,BitVec.ofNat_mul,Nat.mul_comm]
  have noWrap : heap.toNat+amount.toNat+7<2^64:=by rw [amountNumber]; have upper:=frontier.bounded; omega
  obtain ⟨room,funded,same⟩:=PersistentAlloc.global_call_normal_no_wrap source target "wd_rlp_slices" heap amount arrayArguments args installed frontier.cell noWrap normal
  exact ⟨⟨frontier.arena.lower,by rw [amountNumber] at room; omega⟩,by rw [amountNumber] at room; omega,funded,same⟩

def actions : List CallPrefix.Action:=[.declare (ofString "nwd") .one countExpression,.command arrayCall,.declare (ofString "i") .one (.const 0#64)]

theorem prefix_shape : afterTransactionTrie=CallPrefix.program actions loopAndAfter := by
  rw [prefix_shapes.1,prefix_shapes.2.1,prefix_shapes.2.2.1]
  rfl

/-- Allocation is the only clock-spending command in the original count,
array and counter setup. Its real operands come from the count declaration. -/
theorem prefix_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) :
    current.clock-(evaluateHOLFiniteState current (CallPrefix.program actions .skip)).2.clock≤2 := by
  change current.clock-(evaluateHOLFiniteState current (.dec (ofString "nwd") .one countExpression
    (.seq arrayCall (.dec (ofString "i") .one (.const 0#64) .skip)))).2.clock≤2
  apply ClockCost.declared_current current "nwd" countExpression (BitVec.ofNat 64 (Payload.withdrawalCount input)) _ 2 (count_read physical)
  let ready:=bind current "nwd" (BitVec.ofNat 64 (Payload.withdrawalCount input))
  have cell : ready.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 (Payload.withdrawalCount input)))):=bind_lookup_same _ _ _
  exact ClockCost.sequence_current ready arrayCall _ 2 0 (array_cost ready _ physical.data.arena.code cell)
    (ClockCost.declared ready.code (ofString "i") .one (.const 0#64) .skip 0 (ClockCost.skip ready.code))

/-- Every actual withdrawal suffix stops in setup or reaches the literal
encoding loop after executing its real count read, global allocation and
counter initialization. No encoder or later trie success is assumed. -/
theorem to_loop {input : Guest.InputBlob} {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState current afterTransactionTrie=(outcome,post)) :
    (current.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ entered inner,CallPrefix.Execution current actions entered ∧ entered.clock≤current.clock ∧ current.clock-entered.clock≤2 ∧
        post.clock=inner.clock ∧ evaluateHOLFiniteState entered loopAndAfter=(outcome,inner) := by
  have safe : LocalPrefix (ofString "pl") (CallPrefix.program actions .skip):=
    .dec (ofString "nwd") .one countExpression (by decide)
      (.seq (.globalCall (ofString "wd_rlp_slices") (ofString "alloc") arrayArguments)
        (.dec (ofString "i") .one (.const 0#64) (by decide) .skip))
  rw [prefix_shape] at actual
  rcases CallPrefix.priced_trace current post actions loopAndAfter 2 (prefix_cost physical) outcome actual with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value
    rw [stopped.2]
    exact (safe.summary_full current).2.1 value
  · exact Or.inr reached

/-- Actual current withdrawal-loop model. Only the already filled prefix
of the real slice array is described; future rows and allocations are free.
The original decoded input remains before the fresh array and heap. -/
structure LoopModel (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord array : BitVec 64) (boundary count : Nat) where
  index : BitVec 64
  heap : BitVec 64
  slices : Nat→ BitVec 64×BitVec 64
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  countCell : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count)))
  payloadCell : source.locals.lookup (ofString "pl")=some (.val (.word record))
  arrayGlobal : source.globals.lookup (ofString "wd_rlp_slices")=some (.val (.word array))
  bounded : index.toNat≤count
  countCap : count≤335544
  countEq : count=Payload.withdrawalCount input
  data : Data input source pointer si record gasWord boundary
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  arrayArena : AllocatedBytes.Arena array (16*count+16)
  arrayAligned : array.toNat%8=0
  arrayAbove : boundary+32≤array.toNat
  arrayBefore : array.toNat+16*count+16≤heap.toNat
  rows : ∀ row<index.toNat,
    source.memory (array+BitVec.ofNat 64 (16*row))=.word (slices row).1 ∧
    source.memory (array+BitVec.ofNat 64 (16*row+8))=.word (slices row).2
  payload : ∀ row<index.toNat,Mpt.TrieWalk.Payload source.memaddrs (slices row).1 (slices row).2 64
  nonempty : ∀ row<index.toNat,Mpt.CurrentIndexed.NonemptyRow (slices row).1 (slices row).2

def encodeArguments : List (ExpHOL 64):=[.op .add [payloadField 48,.panop .mul [localVar "i",.const 44#64]]]
def footer : ProgHOL 64:=match loopBody with | .decCall _ _ _ _ tail=>tail | _=>.skip

set_option maxRecDepth 100000 in
theorem iteration_shape : loopBody=.decCall (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments footer := by
  simp only [loopBody,loopAndAfter,afterArray,afterCount,afterTransactionTrie,afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    CurrentRlp.Withdrawal.returnShape,encodeArguments,footer,payloadField,Scalar.plus,localVar]

/-- The real row pointer read and actual encoder ABI supply its complete
physical entry from the same current loop model and older copied input. -/
theorem LoopModel.encoder_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (inside : model.index.toNat<count) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) encodeArguments=
      some [.val (.word (pointer+BitVec.ofNat 64 (withdrawalStart input+44*model.index.toNat)))] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "encode_withdrawal_rlp") [.val (.word (pointer+BitVec.ofNat 64 (withdrawalStart input+44*model.index.toNat)))]=
        some (CurrentRlp.Withdrawal.body,callee,CurrentRlp.Withdrawal.returnShape) ∧
      Nonempty (CurrentRlp.Withdrawal.Entry input (callEntryStateHOLFinite source callee) pointer model.heap (withdrawalStart input+44*model.index.toNat)) := by
  have recordRead:=local_word_read source "pl" record model.payloadCell
  have baseRead:=Witness.load_word_read source (Scalar.plus (localVar "pl") 48) (record+48#64) (pointer+BitVec.ofNat 64 (withdrawalStart input))
    (Scalar.plus_read source (localVar "pl") record 48 recordRead)
    (AllocatedBytes.word_mapped source record 136 48 model.data.arena.domain model.data.recordArena (by decide) model.data.recordAligned (by decide))
    (withdrawal_records model.data).1
  have productRead : eval source (.panop .mul [localVar "i",.const 44#64])=some (.val (.word (BitVec.ofNat 64 (44*model.index.toNat)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.indexCell,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm,BitVec.mul_comm]
  have pointerRead : eval source (.op .add [payloadField 48,.panop .mul [localVar "i",.const 44#64]])=
      some (.val (.word (pointer+BitVec.ofNat 64 (withdrawalStart input+44*model.index.toNat)))):=by
    have same:=Scalar.op_congr source .add [payloadField 48,.panop .mul [localVar "i",.const 44#64]]
      [.const (pointer+BitVec.ofNat 64 (withdrawalStart input)),.const (BitVec.ofNat 64 (44*model.index.toNat))]
      (.cons baseRead (.cons productRead .nil))
    rw [same]
    simp [eval,evalHOLExact,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add,BitVec.add_assoc]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) encodeArguments=
      some [.val (.word (pointer+BitVec.ofNat 64 (withdrawalStart input+44*model.index.toNat)))]:=by
    simp only [eval] at pointerRead
    simp only [encodeArguments,evalListHOLFinite,evalListHOLExact,pointerRead]
  obtain ⟨callee,called,wd⟩:=word_environment source.code.lookup (ofString "encode_withdrawal_rlp") (ofString "wd") CurrentRlp.Withdrawal.body CurrentRlp.Withdrawal.returnShape
    (pointer+BitVec.ofNat 64 (withdrawalStart input+44*model.index.toNat)) (CurrentRlp.Withdrawal.original_code source.code model.data.arena.code)
  obtain ⟨oldArray,start,size,block⟩:=model.data.block_inputs
  have beforeRecord:=model.data.copied.beforeRecord
  have recordBefore:=model.data.recordInside.2
  have arrayAbove:=model.arrayAbove
  have arrayBefore:=model.arrayBefore
  have countEq:=model.countEq
  have inputArena : AllocatedBytes.Arena pointer (input.length%2^64):=
    ⟨by have lower:=model.data.copied.lower; omega,by have upper:=model.data.recordArena.upper; omega⟩
  have rowInside : withdrawalStart input+44*model.index.toNat+44≤input.length%2^64:=by
    have rows:=block.data.inside
    have active : model.index.toNat<Payload.withdrawalCount input:=Nat.lt_of_lt_of_le inside (Nat.le_of_eq countEq)
    omega
  exact ⟨callee,args,called,⟨{
    installed:=model.data.arena.code,domain:=model.data.arena.domain,heapCell:=model.heapCell,heapArena:=model.heapArena,heapBound:=model.heapBound,heapAligned:=model.heapAligned
    inputArena:=inputArena,inputBefore:=by omega,image:=model.data.copied.bytes,inside:=rowInside,wdCell:=wd }⟩⟩

/-- The real current encoder call in any active iteration costs202 ticks
including its caller, without assuming its buffer allocation succeeds. -/
theorem LoopModel.encoder_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (inside : model.index.toNat<count) :
    source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString "e"),none)) (ofString "encode_withdrawal_rlp") encodeArguments)).2.clock≤202 := by
  obtain ⟨callee,args,called,⟨entry⟩⟩:=model.encoder_entry inside
  exact ClockCost.call_current source (some (some (ofString "e"))) (ofString "encode_withdrawal_rlp") encodeArguments _ CurrentRlp.Withdrawal.body callee CurrentRlp.Withdrawal.returnShape 201
    args called (CurrentRlp.Withdrawal.body_cost entry)

def pointerAddress : ExpHOL 64:=.op .add [.var .global (ofString "wd_rlp_slices"),.panop .mul [localVar "i",.const 16#64]]
def lengthAddress : ExpHOL 64:=.op .add [.var .global (ofString "wd_rlp_slices"),.panop .mul [localVar "i",.const 16#64],.const 8#64]
def increment : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])

set_option maxRecDepth 100000 in
theorem footer_shape : footer=.seq (.store pointerAddress (.rfield 0 (localVar "e"))) (.seq (.store lengthAddress (.rfield 1 (localVar "e"))) increment) := by
  simp only [footer,loopBody,loopAndAfter,afterArray,afterCount,afterTransactionTrie,afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,pointerAddress,lengthAddress,increment,payloadField,Scalar.plus,localVar]

theorem footer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) : source.clock-(evaluateHOLFiniteState source footer).2.clock≤0 := by
  have store1:=ClockCost.store source.code pointerAddress (.rfield 0 (localVar "e"))
  have store2:=ClockCost.store source.code lengthAddress (.rfield 1 (localVar "e"))
  have advanced : ClockCost.Bound source.code increment 0:=ClockCost.of_quiet source.code increment (QuietClock.assign source.code _ _)
  rw [footer_shape]
  exact ClockCost.sequence source.code _ _ 0 0 store1 (ClockCost.sequence source.code _ _ 0 0 store2 advanced) source rfl

/-- One complete actual encoding iteration costs202body source ticks on
all outcomes. Stores and increment spend no source clock; failed stores
need no later successful row, counter or loop invariant. -/
theorem LoopModel.iteration_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (inside : model.index.toNat<count) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤202 := by
  obtain ⟨callee,args,called,⟨entry⟩⟩:=model.encoder_entry inside
  rw [iteration_shape]
  exact ClockCost.scoped_reached_current source "e" CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments _ CurrentRlp.Withdrawal.body footer
    callee CurrentRlp.Withdrawal.returnShape 201 0 args called (CurrentRlp.Withdrawal.body_cost entry) (by
      intro child returned normal checked
      exact footer_cost (CallNormal.continuationEntry source child "e" returned))

/-- Actual normal encoder output immediately before the two array stores.
The next heap and whole decoded input follow from the same call, while its
original caller locals are restored with the genuine encoded pair in e. -/
structure EncodedRow {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (target : PanSemStateFiniteExact 64 Guest.HostMemory) where
  length : Nat
  positive : 1≤length
  bounded : length≤57
  locals : target.locals=source.locals.update (ofString "e",.rStruct [.val (.word model.heap),.val (.word (BitVec.ofNat 64 length))])
  metadata : MemoryMetadata.erase target=MemoryMetadata.erase (PersistentAlloc.post source model.heap 64#64)
  owned : AllocatedBytes.Arena model.heap 64
  room : model.heap.toNat+64≤2952790016
  number : (PersistentAlloc.rounded model.heap 64#64).toNat=model.heap.toNat+64
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded model.heap 64#64)))
  data : Data input target pointer si record gasWord boundary
  older : ∀ query : BitVec 64,query.toNat<model.heap.toNat→ target.memory query=source.memory query

theorem LoopModel.encoder_output {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (inside : model.index.toNat<count)
    (reached : CallPrefix.Reaches source (.scoped (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments) target) :
    Nonempty (EncodedRow model target) := by
  obtain ⟨callee,args,called,⟨entry⟩⟩:=model.encoder_entry inside
  obtain ⟨child,returned,run,endpoint⟩:=CallPrefix.Reaches.scoped_known (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments _
    CurrentRlp.Withdrawal.body callee CurrentRlp.Withdrawal.returnShape args called reached
  obtain ⟨length,positive,bounded,answer,owned,room,metadata,memory⟩:=CurrentRlp.Withdrawal.body_normal entry returned run
  have localFrame : target.locals=source.locals.update (ofString "e",.rStruct [.val (.word model.heap),.val (.word (BitVec.ofNat 64 length))]):=by
    rw [endpoint,answer]
    rfl
  have targetMetadata : MemoryMetadata.erase target=MemoryMetadata.erase (PersistentAlloc.post source model.heap 64#64):=by
    rw [endpoint]
    exact metadata
  have globals:=congrArg PanSemStateFiniteExact.globals targetMetadata
  change target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded model.heap 64#64))) at globals
  have domain:=MemoryMetadata.domain targetMetadata
  change target.memaddrs=source.memaddrs at domain
  have endian:=MemoryMetadata.endian targetMetadata
  change target.be=source.be at endian
  have code:=MemoryMetadata.code targetMetadata
  change target.code=source.code at code
  have noWrap : model.heap.toNat+(64#64 : BitVec 64).toNat+7<2^64:=by have upper:=model.heapBound; change model.heap.toNat+64+7<2^64; omega
  have number : (PersistentAlloc.rounded model.heap 64#64).toNat=model.heap.toNat+64:=by
    rw [PersistentAlloc.rounded_nat model.heap 64#64 noWrap]
    have aligned:=model.heapAligned
    change (model.heap.toNat+64+7)/8*8=model.heap.toNat+64
    omega
  have cell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded model.heap 64#64))):=by
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have kept : HeapGlobals source target:=by
    intro name other
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have siLocal : target.locals.lookup (ofString "si")=some (.val (.word si)):=by
    rw [localFrame]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using model.data.siLocal
  have older (query : BitVec 64) (before : query.toNat<model.heap.toNat) : target.memory query=source.memory query:=by
    rw [endpoint]
    exact memory query (owned.away_below model.heap query 64 model.heapAligned before)
  have heap : NormalHeapEffects.AtLeast (boundary+32) target:=⟨PersistentAlloc.rounded model.heap 64#64,cell,
    by rw [number]; have lower:=model.arrayAbove; have before:=model.arrayBefore; omega,
    by rw [number]; exact room,by rw [number]; have aligned:=model.heapAligned; omega⟩
  have data:=model.data.of_heap_frame domain endian code kept heap siLocal (fun query lower before=>older query (by
    have a:=model.arrayAbove; have b:=model.arrayBefore; omega))
  exact ⟨{length:=length,positive:=positive,bounded:=bounded,locals:=localFrame,metadata:=targetMetadata,owned:=owned,room:=room,number:=number,heapCell:=cell,data:=data,older:=older}⟩

def footerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array index pointer : BitVec 64) (length : Nat) :=
  bind {source with memory:=(StoreWord.put (StoreWord.put source.memory (array+BitVec.ofNat 64 (16*index.toNat)) pointer)
    (array+BitVec.ofNat 64 (16*index.toNat+8)) (BitVec.ofNat 64 length))} "i" (index+1#64)

/-- Natural addresses of both actual slice-array words, including the
extra reserved row. The array's own allocation supplies all no-wrap room. -/
theorem LoopModel.row_numbers {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (row : Nat) (inside : row≤count) :
    (array+BitVec.ofNat 64 (16*row)).toNat=array.toNat+16*row ∧
      (array+BitVec.ofNat 64 (16*row+8)).toNat=array.toNat+16*row+8 := by
  have upper:=model.arrayArena.upper
  exact ⟨byteAddress_toNat array (16*row) (by omega),by
    have number:=byteAddress_toNat array (16*row+8) (by omega)
    change (array+BitVec.ofNat 64 (16*row+8)).toNat=array.toNat+(16*row+8) at number
    omega⟩

/-- The real two stores and increment execute from the same observed
encoded pair and owned array. Their exact state describes only this row. -/
theorem LoopModel.footer_execute {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (encoded : EncodedRow model current)
    (inside : model.index.toNat<count) :
    evaluateHOLFiniteState current footer=(none,footerState current array model.index model.heap encoded.length) := by
  have globals:=congrArg PanSemStateFiniteExact.globals encoded.metadata
  change current.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded model.heap 64#64))) at globals
  have arrayCell : current.globals.lookup (ofString "wd_rlp_slices")=some (.val (.word array)):=by
    rw [globals]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using model.arrayGlobal
  have iCell : current.locals.lookup (ofString "i")=some (.val (.word model.index)):=by
    rw [encoded.locals]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using model.indexCell
  have eCell : current.locals.lookup (ofString "e")=some (.rStruct [.val (.word model.heap),.val (.word (BitVec.ofNat 64 encoded.length))]):=by
    rw [encoded.locals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have pointerRead : eval current pointerAddress=some (.val (.word (array+BitVec.ofNat 64 (16*model.index.toNat)))):=by
    simp [eval,pointerAddress,evalHOLExact,evalListHOLExact,toExact,localVar,arrayCell,iCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,Nat.mul_comm,BitVec.mul_comm]
  have lengthRead : eval current lengthAddress=some (.val (.word (array+BitVec.ofNat 64 (16*model.index.toNat+8)))):=by
    simp [eval,lengthAddress,evalHOLExact,evalListHOLExact,toExact,localVar,arrayCell,iCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm,BitVec.mul_comm,BitVec.add_assoc]
  have valueRead : eval current (.rfield 0 (localVar "e"))=some (.val (.word model.heap)):=by
    simp [eval,evalHOLExact,toExact,localVar,eCell]
  have sizeRead : eval current (.rfield 1 (localVar "e"))=some (.val (.word (BitVec.ofNat 64 encoded.length))):=by
    simp [eval,evalHOLExact,toExact,localVar,eCell]
  have pointerMapped : current.memaddrs (array+BitVec.ofNat 64 (16*model.index.toNat)):=AllocatedBytes.word_mapped current array (16*count+16) (16*model.index.toNat)
    encoded.data.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  have lengthMapped : current.memaddrs (array+BitVec.ofNat 64 (16*model.index.toNat+8)):=AllocatedBytes.word_mapped current array (16*count+16) (16*model.index.toNat+8)
    encoded.data.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  let sp:={current with memory:=StoreWord.put current.memory (array+BitVec.ofNat 64 (16*model.index.toNat)) model.heap}
  have pointerRun : evaluateHOLFiniteState current (.store pointerAddress (.rfield 0 (localVar "e")))=(none,sp):=
    StoreWord.execute current pointerAddress (.rfield 0 (localVar "e")) _ model.heap pointerRead valueRead pointerMapped
  have lengthReadP : eval sp lengthAddress=some (.val (.word (array+BitVec.ofNat 64 (16*model.index.toNat+8)))):=lengthRead
  have sizeReadP : eval sp (.rfield 1 (localVar "e"))=some (.val (.word (BitVec.ofNat 64 encoded.length))):=sizeRead
  let sl:={sp with memory:=StoreWord.put sp.memory (array+BitVec.ofNat 64 (16*model.index.toNat+8)) (BitVec.ofNat 64 encoded.length)}
  have lengthRun : evaluateHOLFiniteState sp (.store lengthAddress (.rfield 1 (localVar "e")))=(none,sl):=
    StoreWord.execute sp lengthAddress (.rfield 1 (localVar "e")) _ (BitVec.ofNat 64 encoded.length) lengthReadP sizeReadP lengthMapped
  have incrementRead : eval sl (.op .add [localVar "i",.const 1#64])=some (.val (.word (model.index+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,show sl.locals.lookup (ofString "i")=some (.val (.word model.index)) from iCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have advanced:=StateSteps.assign_execute sl "i" (.op .add [localVar "i",.const 1#64]) model.index (model.index+1#64) iCell incrementRead
  rw [footer_shape,evaluateHOLFiniteState_seq_line780,pointerRun]
  change evaluateHOLFiniteState sp (.seq (.store lengthAddress (.rfield 1 (localVar "e"))) increment)=_
  rw [evaluateHOLFiniteState_seq_line780,lengthRun]
  exact advanced

/-- The two actual new row words have their just-written values. -/
theorem LoopModel.footer_cells {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count)
    (current : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) :
    (footerState current array model.index model.heap length).memory (array+BitVec.ofNat 64 (16*model.index.toNat))=.word model.heap ∧
      (footerState current array model.index model.heap length).memory (array+BitVec.ofNat 64 (16*model.index.toNat+8))=.word (BitVec.ofNat 64 length) := by
  have numbers:=model.row_numbers model.index.toNat model.bounded
  have different : array+BitVec.ofNat 64 (16*model.index.toNat)≠array+BitVec.ofNat 64 (16*model.index.toNat+8):=by
    intro same
    have equality:=congrArg BitVec.toNat same
    omega
  exact ⟨by change StoreWord.put (StoreWord.put current.memory _ model.heap) _ (BitVec.ofNat 64 length) _=_; simp [StoreWord.put,different],by exact if_pos rfl⟩

/-- Actual footer writes preserve all older rows and every word before
its current row; buffer encoding and source clocks play no role here. -/
theorem LoopModel.footer_prefix {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count)
    (current : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (query : BitVec 64) (before : query.toNat<array.toNat+16*model.index.toNat) :
    (footerState current array model.index model.heap length).memory query=current.memory query := by
  have numbers:=model.row_numbers model.index.toNat model.bounded
  have notPointer : query≠array+BitVec.ofNat 64 (16*model.index.toNat):=by
    intro same
    have equality:=congrArg BitVec.toNat same
    omega
  have notLength : query≠array+BitVec.ofNat 64 (16*model.index.toNat+8):=by
    intro same
    have equality:=congrArg BitVec.toNat same
    omega
  change StoreWord.put (StoreWord.put current.memory _ model.heap) _ (BitVec.ofNat 64 length) query=current.memory query
  simp [StoreWord.put,notPointer,notLength]

/-- The actual footer completes exactly one initialized prefix row and
retains the decoded inputs, all older rows, real next heap and globals. -/
theorem LoopModel.after_footer {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (encoded : EncodedRow model current)
    (inside : model.index.toNat<count) :
    ∃ next : LoopModel input (restore source "e" (footerState current array model.index model.heap encoded.length)) pointer si record gasWord array boundary count,
      next.index=model.index+1#64 ∧ next.heap=PersistentAlloc.rounded model.heap 64#64 ∧
      HeapGlobals source (restore source "e" (footerState current array model.index model.heap encoded.length)) ∧
      ∀ query : BitVec 64,query.toNat<array.toNat→ (restore source "e" (footerState current array model.index model.heap encoded.length)).memory query=source.memory query := by
  let final:=restore source "e" (footerState current array model.index model.heap encoded.length)
  let nextHeap:=PersistentAlloc.rounded model.heap 64#64
  let slices:=Function.update model.slices model.index.toNat (model.heap,BitVec.ofNat 64 encoded.length)
  have indexNumber : (model.index+1#64).toNat=model.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have small:=model.countCap; omega)]
    rfl
  have saved (name : String) (notIndex : ofString "i"≠ofString name) (notE : ofString "e"≠ofString name) :
      final.locals.lookup (ofString name)=current.locals.lookup (ofString name):=
    (restore_lookup_other source _ "e" name (Ne.symm notE)).trans (bind_lookup_other _ "i" name _ notIndex)
  have oldSaved (name : String) (notE : ofString "e"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [encoded.locals]
    simp [HolFiniteMapExact.update,FUPDATE,notE]
  have iCell : final.locals.lookup (ofString "i")=some (.val (.word (model.index+1#64))):=
    (restore_lookup_other source _ "e" "i" (by decide)).trans (bind_lookup_same _ _ _)
  have siCell : final.locals.lookup (ofString "si")=some (.val (.word si)):=
    (saved "si" (by decide) (by decide)).trans encoded.data.siLocal
  have data : Data input final pointer si record gasWord boundary:=encoded.data.of_metadata (target:=final) rfl siCell (by
    intro query lower before
    exact model.footer_prefix current encoded.length query (by have above:=model.arrayAbove; omega))
  have domain : final.memaddrs=source.memaddrs:=data.arena.domain.trans model.data.arena.domain.symm
  have globals:=congrArg PanSemStateFiniteExact.globals encoded.metadata
  change current.globals=source.globals.update (ofString "heap_ptr",.val (.word nextHeap)) at globals
  have kept : HeapGlobals source final:=by
    intro name other
    change current.globals.lookup name=source.globals.lookup name
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have rowFrame (row : Nat) (before : row<model.index.toNat) :
      final.memory (array+BitVec.ofNat 64 (16*row))=source.memory (array+BitVec.ofNat 64 (16*row)) ∧
      final.memory (array+BitVec.ofNat 64 (16*row+8))=source.memory (array+BitVec.ofNat 64 (16*row+8)):=by
    have numbers:=model.row_numbers row (Nat.le_trans (Nat.le_of_lt before) model.bounded)
    have arrayBefore:=model.arrayBefore
    constructor
    · exact (model.footer_prefix current encoded.length _ (by rw [numbers.1]; omega)).trans (encoded.older _ (by rw [numbers.1]; have bound:=model.bounded; omega))
    · exact (model.footer_prefix current encoded.length _ (by rw [numbers.2]; omega)).trans (encoded.older _ (by rw [numbers.2]; have bound:=model.bounded; omega))
  have lengthNumber : (BitVec.ofNat 64 encoded.length).toNat=encoded.length:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=encoded.bounded; omega)]
  have newPayload : Mpt.TrieWalk.Payload final.memaddrs model.heap (BitVec.ofNat 64 encoded.length) 64:=by
    refine ⟨by rw [lengthNumber]; have small:=encoded.bounded; omega,?_,?_⟩
    · rw [lengthNumber]; have room:=encoded.room; have small:=encoded.bounded; omega
    · intro offset within
      exact AllocatedBytes.byte_mapped final model.heap 64 offset data.arena.domain encoded.owned (by rw [lengthNumber] at within; have small:=encoded.bounded; omega)
  have newNonempty : Mpt.CurrentIndexed.NonemptyRow model.heap (BitVec.ofNat 64 encoded.length):=by
    constructor
    · intro zero
      have lower:=encoded.owned.lower
      rw [zero] at lower
      change 2701131776≤0 at lower
      omega
    · intro zero
      have valueZero:=congrArg BitVec.toNat zero
      rw [lengthNumber] at valueZero
      change encoded.length=0 at valueZero
      have positive:=encoded.positive
      omega
  let next : LoopModel input final pointer si record gasWord array boundary count:={
    index:=model.index+1#64,heap:=nextHeap,slices:=slices,indexCell:=iCell
    countCell:=(saved "nwd" (by decide) (by decide)).trans ((oldSaved "nwd" (by decide)).trans model.countCell)
    payloadCell:=(saved "pl" (by decide) (by decide)).trans ((oldSaved "pl" (by decide)).trans model.payloadCell)
    arrayGlobal:=(kept _ (by decide)).trans model.arrayGlobal
    bounded:=by rw [indexNumber]; omega,countCap:=model.countCap,countEq:=model.countEq,data:=data,heapCell:=encoded.heapCell
    heapArena:=⟨by rw [encoded.number]; have lower:=model.heapArena.lower; omega,by rw [encoded.number]; have room:=encoded.room; omega⟩
    heapBound:=by rw [encoded.number]; exact encoded.room
    heapAligned:=by rw [encoded.number]; have aligned:=model.heapAligned; omega
    arrayArena:=model.arrayArena,arrayAligned:=model.arrayAligned,arrayAbove:=model.arrayAbove
    arrayBefore:=by rw [encoded.number]; have old:=model.arrayBefore; omega
    rows:=by
      intro row before
      by_cases same : row=model.index.toNat
      · subst row
        simpa only [slices,Function.update_self,final,restore] using model.footer_cells current encoded.length
      · have old : row<model.index.toNat:=by rw [indexNumber] at before; omega
        obtain ⟨pointerFrame,lengthFrame⟩:=rowFrame row old
        obtain ⟨pointerStored,lengthStored⟩:=model.rows row old
        simpa [slices,Function.update,same] using And.intro (pointerFrame.trans pointerStored) (lengthFrame.trans lengthStored)
    payload:=by
      intro row before
      by_cases same : row=model.index.toNat
      · subst row; simpa only [slices,Function.update_self] using newPayload
      · have old : row<model.index.toNat:=by rw [indexNumber] at before; omega
        have prior:=model.payload row old
        rw [domain]
        simpa [slices,Function.update,same] using prior
    nonempty:=by
      intro row before
      by_cases same : row=model.index.toNat
      · subst row; simpa only [slices,Function.update_self] using newNonempty
      · have old : row<model.index.toNat:=by rw [indexNumber] at before; omega
        simpa [slices,Function.update,same] using model.nonempty row old }
  refine ⟨next,rfl,rfl,kept,?_⟩
  intro query before
  exact (model.footer_prefix current encoded.length query (by omega)).trans (encoded.older query (by have bound:=model.arrayBefore; omega))

/-- Clock-only entry changes retain the same real memory and inputs.
This is used solely for the evaluator's actual while-loop clock decrement. -/
def LoopModel.clocked {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (clock : Nat) :
    LoopModel input {source with clock:=clock} pointer si record gasWord array boundary count :=
  {model with data:=model.data.of_frame rfl model.data.siLocal}

/-- Every genuine normally continuing current withdrawal iteration fills
one real row, increments its actual counter and derives the next complete
loop model. No later row, encoder or allocation is assumed successful. -/
theorem LoopModel.iteration_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (inside : model.index.toNat<count)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ next : LoopModel input target pointer si record gasWord array boundary count,
      next.index=model.index+1#64 ∧ next.heap=PersistentAlloc.rounded model.heap 64#64 ∧ HeapGlobals source target ∧
      ∀ query : BitVec 64,query.toNat<array.toNat→ target.memory query=source.memory query := by
  obtain ⟨callee,args,called,⟨entry⟩⟩:=model.encoder_entry inside
  rw [iteration_shape] at normal
  obtain ⟨funded,child,returned,inner,run,checked,remaining,endpoint⟩:=CallNormal.scoped_none source target "e" CurrentRlp.Withdrawal.returnShape
    (ofString "encode_withdrawal_rlp") encodeArguments _ CurrentRlp.Withdrawal.body footer callee CurrentRlp.Withdrawal.returnShape args called normal
  let current:=CallNormal.continuationEntry source child "e" returned
  have reached : CallPrefix.Reaches source (.scoped (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments) current:=
    .scoped source (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments _ CurrentRlp.Withdrawal.body callee CurrentRlp.Withdrawal.returnShape
      returned child args called (by omega) run checked
  obtain ⟨encoded⟩:=model.encoder_output inside reached
  have executed:=model.footer_execute encoded inside
  have innerEq : inner=footerState current array model.index model.heap encoded.length:=congrArg Prod.snd (remaining.symm.trans executed)
  obtain ⟨next,indexEq,heapEq,globals,memory⟩:=model.after_footer encoded inside
  rw [endpoint,innerEq]
  exact ⟨next,indexEq,heapEq,globals,memory⟩

theorem loop_body_limit : LocalPrefix (ofString "nwd") loopBody := by
  rw [iteration_shape,footer_shape]
  exact .decCall (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments (by decide)
    (.seq (.store pointerAddress (.rfield 0 (localVar "e")))
      (.seq (.store lengthAddress (.rfield 1 (localVar "e"))) (.assign (ofString "i") _ (by decide))))

def loopRank (count : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  count-(CounterFlow.counterWord source (ofString "i")).toNat

theorem LoopModel.rank {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) : loopRank count source=count-model.index.toNat := by
  simp [loopRank,CounterFlow.counterWord,model.indexCell,valueWord]

theorem LoopModel.test_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) :
    eval source test=some (.val (.word (if model.index.toNat<count then 1#64 else 0#64))) := by
  exact SignedGuardedCounterLoop.test_read (ofString "nwd") count (by have small:=model.countCap; omega) source model.index model.indexCell model.countCell model.bounded

theorem LoopModel.active_of_test {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<count := by
  by_contra inactive
  have expected:=model.test_read
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- Every current withdrawal-loop outcome is priced by its actual
remaining row count. Only a same-run normal iteration supplies the next
model and strictly smaller rank; failed rows need no future model. -/
theorem LoopModel.loop_cost_ranked {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤203*loopRank count source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel input current pointer si record gasWord array boundary count)
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2.clock≤202:=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=live.active_of_test word read nonzero
    exact (live.clocked (current.clock-1)).iteration_cost active
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→ word≠0#64→
      0<loopRank count current ∧ (current.clock≠0→ let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
        (output.1=none ∨ output.1=some .continue)→ invariant output.2 ∧ loopRank count output.2<loopRank count current):=by
    intro current codeEq valid word read nonzero
    obtain ⟨live⟩:=valid
    have active:=live.active_of_test word read nonzero
    have before:=live.rank
    refine ⟨by rw [before]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((loop_body_limit.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,heapEq,globals,memory⟩:=(live.clocked (current.clock-1)).iteration_normal active run
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have small:=live.countCap; omega)]
      rfl
    have nextNumber : next.index.toNat=live.index.toNat+1:=(congrArg BitVec.toNat indexEq).trans number
    refine ⟨⟨next⟩,?_⟩
    rw [next.rank,nextNumber,before]
    omega
  exact ClockCost.ranked_loop_current source.code test loopBody 202 invariant (loopRank count) priced progress source rfl ⟨model⟩

theorem LoopModel.loop_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤203*count := by
  exact Nat.le_trans model.loop_cost_ranked (Nat.mul_le_mul_left 203 (by rw [model.rank]; omega))

theorem LoopModel.loop_uniform {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤68115432 := by
  have priced:=model.loop_cost
  have small:=model.countCap
  omega

/-- A real normally exiting complete loop checked every original row,
retains the complete final array model and preserves all older caller data. -/
theorem LoopModel.loop_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count)
    (normal : evaluateHOLFiniteState source (.while test loopBody)=(none,post)) :
    ∃ final : LoopModel input post pointer si record gasWord array boundary count,final.index.toNat=count ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,query.toNat<array.toNat→ post.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel input current pointer si record gasWord array boundary count,
    HeapGlobals source current ∧ ∀ query : BitVec 64,query.toNat<array.toNat→ current.memory query=source.memory query
  have initial : invariant source:=⟨model,by intro name other; rfl,by intros; rfl⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,target)→ invariant target:=by
    intro current codeEq valid word read nonzero funded target bodyRun
    obtain ⟨live,globals,memory⟩:=valid
    obtain ⟨next,indexEq,heapEq,nextGlobals,nextMemory⟩:=(live.clocked (current.clock-1)).iteration_normal (live.active_of_test word read nonzero) bodyRun
    exact ⟨next,fun name other=>(nextGlobals name other).trans (globals name other),
      fun query before=>(nextMemory query before).trans (memory query before)⟩
  obtain ⟨final,globals,memory⟩:=loop_invariant_no_control source.code test loopBody
    (fun current=>(loop_body_limit.summary_full current).2.2) invariant step source post rfl initial normal
  have exited:=loop_normal_exit test loopBody (fun current=>(loop_body_limit.summary_full current).2.2.1) source post normal
  have expected:=final.test_read
  have exactCount : final.index.toNat=count:=by
    by_cases active : final.index.toNat<count
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · have bounded:=final.bounded
      omega
  exact ⟨final,exactCount,globals,memory⟩

/-- At the real normal loop exit the complete initialized array satisfies
the current indexed trie's owned, bounded, nonempty-row entry contract. -/
theorem LoopModel.completed_slices {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (finished : model.index.toNat=count) :
    Mpt.Indexed.SliceArray source array count model.heap.toNat 64 model.slices Mpt.CurrentIndexed.NonemptyRow := by
  constructor
  · intro active
    exact model.arrayArena.weaken array (16*count+16) (16*count) (by omega)
  · intro active
    exact model.arrayAligned
  · intro active
    have above:=model.arrayAbove
    have lower:=model.data.recordInside.1
    have before:=model.data.recordInside.2
    omega
  · intro active
    have before:=model.arrayBefore
    omega
  · intro row inside
    have stored:=model.rows row (by rw [finished]; exact inside)
    simpa only [VarList.row,VarList.lengthCell,BitVec.ofNat_add,BitVec.add_assoc] using stored
  · intro row inside
    exact model.payload row (by rw [finished]; exact inside)
  · intro row inside
    exact model.nonempty row (by rw [finished]; exact inside)

/-- Main's actual count/global-array/counter execution establishes the
initial loop model with no initialized rows. The checked allocation supplies
its own capacity; the original copied input and header remain older. -/
theorem setup_model {input : Guest.InputBlob} {source current entered : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (small : Payload.withdrawalCount input≤335544) (execution : CallPrefix.Execution current actions entered) :
    ∃ model : LoopModel input entered pointer si record gasWord (headerFrontier header) boundary (Payload.withdrawalCount input),model.index=0#64 ∧ (∀ query : BitVec 64,entered.memory query=current.memory query) ∧
      ∀ name : String,ofString "nwd"≠ofString name→ ofString "i"≠ofString name→ entered.locals.lookup (ofString name)=current.locals.lookup (ofString name) := by
  let count:=Payload.withdrawalCount input
  let array:=headerFrontier header
  let amount:=BitVec.ofNat 64 (16*count+16)
  let ready:=bind current "nwd" (BitVec.ofNat 64 count)
  have afterCount:=execution.declare_next (.val (.word (BitVec.ofNat 64 count))) (count_read physical)
  obtain ⟨allocated,normal,tail⟩:=afterCount.command_next arrayCall _
  have readyFrontier : HeapFrontier ready header array:=physical.frontier.of_globals current ready header array rfl
  have countCell : ready.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
  obtain ⟨owned,room,funded,allocatedEq⟩:=array_normal header array count readyFrontier small physical.data.arena.code countCell normal
  rw [allocatedEq] at tail
  have last:=tail.declare_next (.val (.word 0#64)) rfl
  let actual:=bind (putGlobal (PersistentAlloc.post {ready with clock:=ready.clock-1} array amount) "wd_rlp_slices" array) "i" 0#64
  have enteredEq : entered=actual:=by cases last; rfl
  have arrayAbove : boundary+32≤array.toNat:=by
    have before:=physical.before
    have afterHeader:=physical.frontier.afterHeader
    change boundary+32≤(headerFrontier header).toNat
    omega
  have amountNumber : amount.toNat=16*count+16:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [count]; omega)]
  have noWrap : array.toNat+amount.toNat+7<2^64:=by
    rw [amountNumber]
    have bounded:=physical.frontier.bounded
    dsimp [count] at *
    omega
  let nextHeap:=PersistentAlloc.rounded array amount
  have number : nextHeap.toNat=array.toNat+16*count+16:=by
    rw [PersistentAlloc.rounded_nat array amount noWrap,amountNumber]
    have aligned:=physical.frontier.aligned
    change array.toNat%8=0 at aligned
    omega
  have heapCell : entered.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)):=by
    rw [enteredEq]
    simp [actual,putGlobal,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,nextHeap]
  have siCell : entered.locals.lookup (ofString "si")=some (.val (.word si)):=by
    rw [enteredEq]
    simpa [actual,ready,putGlobal,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using physical.data.siLocal
  let patched:={current with globals:=current.globals.update (ofString "wd_rlp_slices",.val (.word array))}
  have oldData : Data input patched pointer si record gasWord boundary:=by
    apply physical.data.with_globals
    intro name member
    have other : ofString "wd_rlp_slices"≠name:=by
      intro same
      rw [←same] at member
      simpa [dataGlobals,ofString] using member
    simp [HolFiniteMapExact.update,FUPDATE,other]
  have globals : HeapGlobals patched entered:=by
    intro name other
    rw [enteredEq]
    simp [actual,patched,ready,putGlobal,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have heap : NormalHeapEffects.AtLeast (boundary+32) entered:=⟨nextHeap,heapCell,by rw [number]; omega,by rw [number]; omega,
    by rw [number]; have aligned:=physical.frontier.aligned; change array.toNat%8=0 at aligned; omega⟩
  have domain : entered.memaddrs=patched.memaddrs:=by rw [enteredEq]; rfl
  have endian : entered.be=patched.be:=by rw [enteredEq]; rfl
  have code : entered.code=patched.code:=by rw [enteredEq]; rfl
  have data : Data input entered pointer si record gasWord boundary:=oldData.of_heap_frame domain endian code globals heap siCell (by
    intro query lower before
    rw [enteredEq]
    rfl)
  refine ⟨{
    index:=0#64,heap:=nextHeap,slices:=fun _=>(0#64,0#64)
    indexCell:=by rw [enteredEq]; exact bind_lookup_same _ _ _
    countCell:=by
      rw [enteredEq]
      simp [actual,ready,count,putGlobal,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    payloadCell:=by
      rw [enteredEq]
      simpa [actual,ready,putGlobal,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using physical.frame.payload
    arrayGlobal:=by rw [enteredEq]; simp [actual,array,putGlobal,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    bounded:=by simp,countCap:=small,countEq:=rfl,data:=data,heapCell:=heapCell
    heapArena:=⟨by rw [number]; have lower:=owned.lower; omega,by rw [number]; omega⟩
    heapBound:=by rw [number]; omega
    heapAligned:=by rw [number]; have aligned:=physical.frontier.aligned; change array.toNat%8=0 at aligned; omega
    arrayArena:=owned,arrayAligned:=physical.frontier.aligned,arrayAbove:=arrayAbove,arrayBefore:=by rw [number]
    rows:=by simp,payload:=by simp,nonempty:=by simp },rfl,?_,?_⟩
  · intro query; rw [enteredEq]; rfl
  intro name notCount notIndex
  rw [enteredEq]
  exact (bind_lookup_other _ "i" name 0#64 notIndex).trans (bind_lookup_other current "nwd" name (BitVec.ofNat 64 count) notCount)

def rootArguments : List (ExpHOL 64):=[.var .global (ofString "wd_rlp_slices"),localVar "nwd",localVar "wr"]
def rootCall : ProgHOL 64:=.call (some (none,none)) (ofString "build_mpt_indexed") rootArguments
def afterRoot : ProgHOL 64:=match afterLoop with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem root_shape : afterLoop=.seq rootCall afterRoot := by
  simp only [afterLoop,loopAndAfter,afterArray,afterCount,afterTransactionTrie,afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,rootCall,rootArguments,afterRoot,localVar]

/-- The completed actual withdrawal array, latest real heap and retained
startup globals establish every current indexed-builder condition. The
output buffer is the one already allocated by the enclosing header prefix. -/
theorem LoopModel.root_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array out : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (finished : model.index.toNat=count)
    (outCell : source.locals.lookup (ofString "wr")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some (Mpt.Indexed.values array (BitVec.ofNat 64 count) out) ∧
      lookupCodeHOLFinite source.code.lookup (ofString "build_mpt_indexed") (Mpt.Indexed.values array (BitVec.ofNat 64 count) out)=some (Mpt.Indexed.body,callee,.one) ∧
      Nonempty (Mpt.CurrentIndexed.Entry (callEntryStateHOLFinite source callee) array count out 64 model.slices) ∧
      Mpt.CurrentIndexed.RootInputs (callEntryStateHOLFinite source callee) out 2701134640#64 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some (Mpt.Indexed.values array (BitVec.ofNat 64 count) out):=by
    simp [rootArguments,Mpt.Indexed.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.arrayGlobal,model.countCell,outCell]
  obtain ⟨callee,called,arrayLocal,countLocal,outLocal⟩:=Mpt.Indexed.environment source.code.lookup array (BitVec.ofNat 64 count) out (Mpt.Indexed.original_code source.code model.data.arena.code)
  have rows:=model.completed_slices finished
  exact ⟨callee,args,called,⟨{
    heap:=model.heap,arrayCell:=arrayLocal,countCell:=countLocal,outCell:=outLocal,countBound:=by have small:=model.countCap; omega
    domain:=model.data.arena.domain,little:=model.data.little,installed:=model.data.arena.code,keyGlobal:=model.data.mptKey
    heapCell:=model.heapCell,heapArena:=model.heapArena,heapAligned:=model.heapAligned
    heapAbove:=by have a:=model.arrayAbove; have b:=model.arrayBefore; have c:=model.data.recordInside.1; have d:=model.data.recordInside.2; omega
    rows:=rows.of_band source _ array count model.heap.toNat 64 model.slices Mpt.CurrentIndexed.NonemptyRow rfl (by intros; rfl) }⟩,
    {arena:=⟨model.data.arena.scratch,model.data.arena.frame,model.data.arena.domain,model.data.arena.code⟩,emptyGlobal:=model.data.mptEmpty,emptyArena:=⟨by decide,by decide⟩,outArena:=outArena}⟩

/-- The literal withdrawal-trie call is priced by the same actual count,
not the much larger transaction-count specialization. -/
theorem LoopModel.root_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array out : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (finished : model.index.toNat=count)
    (outCell : source.locals.lookup (ofString "wr")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source rootCall).2.clock≤36827*count+12 := by
  obtain ⟨callee,args,called,⟨entry⟩,roots⟩:=model.root_entry finished outCell outArena
  simpa [rootCall,LocalEffects.callInfo,Nat.add_assoc] using ClockCost.call_current source (some none) (ofString "build_mpt_indexed") rootArguments _ Mpt.Indexed.body callee .one
    (36827*count+11) args called (Mpt.CurrentIndexed.body_cost entry roots)

theorem LoopModel.root_uniform {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array out : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (finished : model.index.toNat=count)
    (outCell : source.locals.lookup (ofString "wr")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source rootCall).2.clock≤12357078900 := by
  have priced:=model.root_cost finished outCell outArena
  have small:=model.countCap
  omega

/-- A normal literal withdrawal-trie return forces the actual decoded
withdrawal count to zero and derives its genuine caller/memory frame. -/
theorem LoopModel.root_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array out : BitVec 64} {boundary count : Nat}
    (model : LoopModel input source pointer si record gasWord array boundary count) (finished : model.index.toNat=count)
    (outCell : source.locals.lookup (ofString "wr")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32)
    (normal : evaluateHOLFiniteState source rootCall=(none,target)) :
    Payload.withdrawalCount input=0 ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.locals=source.locals ∧
      ∀ query : BitVec 64,query.toNat<model.heap.toNat→ CopyGeneral.Away out query 32→ target.memory query=source.memory query := by
  obtain ⟨callee,args,called,⟨entry⟩,roots⟩:=model.root_entry finished outCell outArena
  obtain ⟨funded,child,returned,run⟩:=CallNormal.ignored_callee_return source target (ofString "build_mpt_indexed") rootArguments _ Mpt.Indexed.body callee .one args called normal
  obtain ⟨zero,answer,domain,endian,code,heapCell,globals,metadata,memory⟩:=Mpt.CurrentIndexed.body_normal entry roots returned run
  have endpoint:=CallNormal.ignored_target source target (ofString "build_mpt_indexed") rootArguments _ Mpt.Indexed.body callee .one args called returned child run normal
  have heapEq : entry.heap=model.heap:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using entry.heapCell.symm.trans model.heapCell
  rw [endpoint]
  refine ⟨model.countEq.symm.trans zero,metadata,rfl,?_⟩
  intro query before away
  exact memory query (by rw [heapEq]; exact before) away

theorem loop_body_preserves (key : MlS) (notIndex : key≠ofString "i") (notE : key≠ofString "e") : LocalPrefix key loopBody := by
  rw [iteration_shape,footer_shape]
  exact .decCall (ofString "e") CurrentRlp.Withdrawal.returnShape (ofString "encode_withdrawal_rlp") encodeArguments notE
    (.seq (.store pointerAddress (.rfield 0 (localVar "e")))
      (.seq (.store lengthAddress (.rfield 1 (localVar "e"))) (.assign (ofString "i") _ notIndex)))

theorem loop_saved (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS)
    (notIndex : key≠ofString "i") (notE : key≠ofString "e")
    (normal : evaluateHOLFiniteState source (.while test loopBody)=(none,target)) :
    target.locals.lookup key=source.locals.lookup key := by
  have summary:=(LocalPrefix.loop test (loop_body_preserves key notIndex notE)).summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  exact summary.1 rfl

/-- The real suffix through array setup and every withdrawal encoding row
stops within its uniform price or reaches its actual indexed-trie caller.
All rows, caller locals and latest heap come from these same executions. -/
theorem to_after_loop {input : Guest.InputBlob} {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (small : Payload.withdrawalCount input≤335544)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState current afterTransactionTrie=(outcome,post)) :
    (current.clock-post.clock≤68115434 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ next inner,(∃ model : LoopModel input next pointer si record gasWord (headerFrontier header) boundary (Payload.withdrawalCount input),model.index.toNat=Payload.withdrawalCount input) ∧
        next.clock≤current.clock ∧ current.clock-next.clock≤68115434 ∧ post.clock=inner.clock ∧
        next.locals.lookup (ofString "wr")=some (.val (.word (withdrawalBase header))) ∧
        (∀ query : BitVec 64,query.toNat<(headerFrontier header).toNat→ next.memory query=current.memory query) ∧
        (∀ name : String,ofString "nwd"≠ofString name→ ofString "i"≠ofString name→ ofString "e"≠ofString name→ next.locals.lookup (ofString name)=current.locals.lookup (ofString name)) ∧
        evaluateHOLFiniteState next afterLoop=(outcome,inner) := by
  rcases to_loop physical outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨entered,inner,execution,forward,price,endpoint,remaining⟩:=reached
    obtain ⟨model,indexEq,setupMemory,saved⟩:=setup_model physical small execution
    rw [prefix_shapes.2.2.2,evaluateHOLFiniteState_seq_line780] at remaining
    have loopPrice:=model.loop_uniform
    have loopForward:=evaluateHOLFiniteState_clock_le entered (.while test loopBody)
    have never:=((LocalPrefix.loop test loop_body_limit).summary_full entered).2.1
    generalize computed : evaluateHOLFiniteState entered (.while test loopBody)=output at loopPrice loopForward remaining
    obtain ⟨result,next⟩:=output
    change entered.clock-next.clock≤68115432 at loopPrice
    change next.clock≤entered.clock at loopForward
    cases result with
    | none=>
      obtain ⟨final,done,globals,memory⟩:=model.loop_normal computed
      have kept (name : String) (notCount : ofString "nwd"≠ofString name) (notIndex : ofString "i"≠ofString name) (notE : ofString "e"≠ofString name) :
          next.locals.lookup (ofString name)=current.locals.lookup (ofString name):=
        (loop_saved entered next (ofString name) (Ne.symm notIndex) (Ne.symm notE) computed).trans (saved name notCount notIndex)
      exact Or.inr ⟨next,inner,⟨final,done⟩,Nat.le_trans loopForward forward,by omega,endpoint,
        (kept "wr" (by decide) (by decide) (by decide)).trans physical.locals.withdrawals,
        (fun query before=>(memory query before).trans (setupMemory query)),kept,remaining⟩
    | some result=>
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      have observed:=congrArg Prod.fst remaining
      change next.clock=inner.clock at clocks
      refine Or.inl ⟨by rw [endpoint,←clocks]; omega,?_⟩
      intro value returned
      apply never value
      rw [computed]
      exact observed.trans returned

/-- All actual withdrawal work, through its complete indexed-trie caller,
either stops in the uniform price or reaches the real requests suffix with
zero withdrawals, retained decoded inputs and unchanged header cells. -/
theorem to_after_root {input : Guest.InputBlob} {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (small : Payload.withdrawalCount input≤335544)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState current afterTransactionTrie=(outcome,post)) :
    (current.clock-post.clock≤12425194334 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ next inner,Data input next pointer si record gasWord boundary ∧
        NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) next ∧ Payload.withdrawalCount input=0 ∧
        (∀ name : String,ofString "nwd"≠ofString name→ ofString "i"≠ofString name→ ofString "e"≠ofString name→ next.locals.lookup (ofString name)=current.locals.lookup (ofString name)) ∧
        (∀ query : BitVec 64,query.toNat<header.toNat+248→ next.memory query=current.memory query) ∧
        next.clock≤current.clock ∧ current.clock-next.clock≤12425194334 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState next afterRoot=(outcome,inner) := by
  rcases to_after_loop physical small outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨entered,inner,⟨model,finished⟩,forward,price,endpoint,wrCell,older,saved,remaining⟩:=reached
    rw [root_shape,evaluateHOLFiniteState_seq_line780] at remaining
    have rootPrice:=model.root_uniform finished wrCell physical.buffers.withdrawals
    have rootForward:=evaluateHOLFiniteState_clock_le entered rootCall
    have never:=NoReturn.ignored_call (ofString "build_mpt_indexed") rootArguments entered
    generalize computed : evaluateHOLFiniteState entered rootCall=output at rootPrice rootForward remaining
    obtain ⟨result,next⟩:=output
    change entered.clock-next.clock≤12357078900 at rootPrice
    change next.clock≤entered.clock at rootForward
    cases result with
    | none=>
      obtain ⟨zero,metadata,localsEq,memory⟩:=model.root_normal finished wrCell physical.buffers.withdrawals computed
      have numbers:=physical.buffers.numbers header
      have aligned : (withdrawalBase header).toNat%8=0:=by rw [numbers.withdrawals]; have headerAligned:=physical.buffers.ommer.headerAligned; omega
      have inputMemory (query : BitVec 64) (before : query.toNat<boundary) : next.memory query=entered.memory query:=by
        apply memory query
        · have arrayAbove:=model.arrayAbove; have arrayBefore:=model.arrayBefore; omega
        · exact physical.buffers.withdrawals.away_below (withdrawalBase header) query 32 aligned (by rw [numbers.withdrawals]; have headerBefore:=physical.before; omega)
      have retained:=model.data.of_metadata metadata (by rw [localsEq]; exact model.data.siLocal) (fun query lower before=>inputMemory query before)
      have kept (name : String) (notCount : ofString "nwd"≠ofString name) (notIndex : ofString "i"≠ofString name) (notE : ofString "e"≠ofString name) :
          next.locals.lookup (ofString name)=current.locals.lookup (ofString name):=by rw [localsEq]; exact saved name notCount notIndex notE
      have headerMemory (query : BitVec 64) (before : query.toNat<header.toNat+248) : next.memory query=current.memory query:=by
        have first : next.memory query=entered.memory query:=by
          apply memory query
          · have arrayBefore:=model.arrayBefore
            rw [numbers.frontier] at arrayBefore
            omega
          · exact physical.buffers.withdrawals.away_below (withdrawalBase header) query 32 aligned (by rw [numbers.withdrawals]; omega)
        exact first.trans (older query (by rw [numbers.frontier]; omega))
      have globals:=congrArg PanSemStateFiniteExact.globals metadata
      change next.globals=entered.globals at globals
      have heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) next:=
        ⟨model.heap,by rw [globals]; exact model.heapCell,by have before:=model.arrayBefore; omega,model.heapBound,model.heapAligned⟩
      exact Or.inr ⟨next,inner,retained,heapAfter,zero,kept,headerMemory,Nat.le_trans rootForward forward,by omega,endpoint,remaining⟩
    | some result=>
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      have observed:=congrArg Prod.fst remaining
      change next.clock=inner.clock at clocks
      refine Or.inl ⟨by rw [endpoint,←clocks]; omega,?_⟩
      intro value returned
      apply never value
      change (evaluateHOLFiniteState entered rootCall).1=some (.returned value)
      rw [computed]
      exact observed.trans returned

/-- Same-run inputs at the literal execution-requests encoder, after both
actual trie calls. These describe already reached values and owned header
cells; no requests/hash/main success is part of this contract. -/
structure BeforeRequests (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) (header : BitVec 64) (encoded : Nat) : Prop where
  data : Data input current pointer si record gasWord boundary
  heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) current
  transactionsZero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0
  withdrawalsZero : Payload.withdrawalCount input=0
  buffers : HeaderBuffers header
  before : boundary+32≤header.toNat
  geometry : HeaderEncoding.Geometry header (headerFrontier header)
  fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts current.memory header field
  optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts current.memory header field
  headerCell : current.locals.lookup (ofString "h")=some (.val (.word header))
  payloadCell : current.locals.lookup (ofString "pl")=some (.val (.word record))
  requestsCell : current.locals.lookup (ofString "rh")=some (.val (.word (requestsBase header)))
  balanceCell : current.locals.lookup (ofString "bh")=some (.val (.word (balanceBase header)))
  sizeCell : current.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded)))
  sizeBound : encoded≤8388608
  sizeNumber : (BitVec.ofNat 64 encoded).toNat=encoded

/-- Every actual payload-header outcome through both complete indexed
tries is bounded, or reaches the unchanged requests continuation with
zero transactions/withdrawals and all physical header/input conditions. -/
theorem to_before_requests {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤476207133311 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header next inner encoded,BeforeRequests input next pointer si record gasWord boundary header encoded ∧
        next.clock≤source.clock ∧ source.clock-next.clock≤476207133311 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState next afterRoot=(outcome,inner) := by
  rcases PayloadHeaderEntry.to_after_transaction data checked outcome actual with stopped|reached
  · exact Or.inl ⟨by have priced:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,outer,encoded,physical,txZero,encodedBound,wdBound,number,blCell,forward,price,endpoint,remaining⟩:=reached
    rcases to_after_root physical wdBound outcome remaining with stopped|reached
    · exact Or.inl ⟨by have priced:=stopped.1; rw [endpoint]; omega,stopped.2⟩
    · obtain ⟨next,inner,retained,heapAfter,wdZero,saved,memory,nextForward,nextPrice,nextEndpoint,continuation⟩:=reached
      have cells (offset : Nat) (small : offset≤240) : next.memory (HeaderEncoding.address header offset)=entered.memory (HeaderEncoding.address header offset):=by
        apply memory
        have address:=byteAddress_toNat header offset (by have room:=physical.buffers.ommer.headerArena.upper; omega)
        change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at address
        change (header+BitVec.ofNat 64 offset).toNat<header.toNat+248
        omega
      have result : BeforeRequests input next pointer si record gasWord boundary header encoded:={
        data:=retained,heapAfter:=heapAfter,transactionsZero:=txZero,withdrawalsZero:=wdZero,buffers:=physical.buffers,before:=physical.before,geometry:=physical.geometry
        fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells entered.memory next.memory header field cells (physical.fields field member)
        optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells entered.memory next.memory header field cells (physical.optional field member)
        headerCell:=(saved "h" (by decide) (by decide) (by decide)).trans physical.frame.header
        payloadCell:=(saved "pl" (by decide) (by decide) (by decide)).trans physical.frame.payload
        requestsCell:=(saved "rh" (by decide) (by decide) (by decide)).trans physical.locals.requests
        balanceCell:=(saved "bh" (by decide) (by decide) (by decide)).trans physical.locals.balance
        sizeCell:=(saved "bl" (by decide) (by decide) (by decide)).trans blCell,sizeBound:=encodedBound,sizeNumber:=number }
      exact Or.inr ⟨header,next,inner,encoded,result,Nat.le_trans nextForward forward,by omega,endpoint.trans nextEndpoint,continuation⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.prefix_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.withdrawal_records
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.count_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.array_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.array_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.to_loop

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.iteration_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.encoder_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.encoder_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.footer_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.footer_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.iteration_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.encoder_output

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.row_numbers

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.footer_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.footer_cells

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.footer_prefix

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.after_footer

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.iteration_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.loop_body_limit

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.rank

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.test_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.active_of_test

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.loop_cost_ranked

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.loop_uniform

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.completed_slices

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.setup_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.root_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.root_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.root_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.root_uniform

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.LoopModel.root_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.loop_body_preserves

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.loop_saved

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.to_after_loop

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.to_after_root

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderWithdrawals.to_before_requests
