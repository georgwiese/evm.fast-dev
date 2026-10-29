import InitECandidate.Solver.Input.CurrentVerify.IndexedTransactions
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.Input.ClockCostAssignedCurrent
import InitECandidate.Solver.Input.CurrentRlp.Withdrawal
import InitECandidate.Solver.Input.CallPrefixScopedActual

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
  slices : Nat→BitVec 64×BitVec 64
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
  older : ∀ query : BitVec 64,query.toNat<model.heap.toNat→target.memory query=source.memory query

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
