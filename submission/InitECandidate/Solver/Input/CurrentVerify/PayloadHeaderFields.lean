import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderFrame
import InitECandidate.Solver.Input.RlpWrite.U256Store

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def afterFixedHeader : List CallPrefix.Action:=afterOmmerHash.drop 3
def ommerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  putHeader hashed heap 16 (ommerBase heap)
def beneficiaryStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  putHeader (ommerStored hashed heap) heap 24 (pointer+62#64+32#64)
def stateRootStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  putHeader (beneficiaryStored hashed pointer heap) heap 32 (pointer+62#64+52#64)

set_option maxRecDepth 100000 in
theorem fixed_header_actions : afterOmmerHash=
    .command (storeField 16 (localVar "oh"))::
    .command (storeField 24 (Scalar.plus (localVar "raw") 32))::
    .command (storeField 32 (Scalar.plus (localVar "raw") 52))::afterFixedHeader := by
  simp only [afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterFixedHeader,storeField,headerField,Scalar.plus,localVar]
  rfl

theorem fixed_header_from_execution (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput source pointer record heap hashed)
    (execution : CallPrefix.Execution hashed afterOmmerHash current) :
    HeaderFrame source (stateRootStored hashed pointer heap) pointer record heap ∧
      CallPrefix.Execution (stateRootStored hashed pointer heap) afterFixedHeader current := by
  rw [fixed_header_actions] at execution
  have frame:=HeaderFrame.of_ommer source hashed pointer record heap layout output
  have ohCell : hashed.locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))):=
    (output.locals _).trans (ommer_local source pointer record heap)
  have ohRead : eval hashed (localVar "oh")=some (.val (.word (ommerBase heap))):=by
    simp [eval,evalHOLExact,toExact,localVar,ohCell]
  have first:=store_field_execute hashed heap 16 (ommerBase heap) (localVar "oh") output.environment.domain
    layout.headerArena layout.headerAligned (by decide) (by decide) frame.header ohRead
  have firstTrace:=execution.command_known _ _ first
  have frame1:=frame.stored source hashed pointer record heap 16 (ommerBase heap) layout.headerArena (by decide)
  have rawRead : eval (ommerStored hashed heap) (localVar "raw")=some (.val (.word (pointer+62#64))):=by
    have cell : (ommerStored hashed heap).locals.lookup (ofString "raw")=some (.val (.word (pointer+62#64))):=frame1.raw
    simp [eval,evalHOLExact,toExact,localVar,cell]
  have second:=store_field_execute (ommerStored hashed heap) heap 24 (pointer+62#64+32#64)
    (Scalar.plus (localVar "raw") 32) output.environment.domain layout.headerArena layout.headerAligned (by decide) (by decide) frame1.header
    (Scalar.plus_read _ _ _ 32 rawRead)
  have secondTrace:=firstTrace.command_known _ _ second
  have frame2:=frame1.stored source _ pointer record heap 24 (pointer+62#64+32#64) layout.headerArena (by decide)
  have rawRead2 : eval (beneficiaryStored hashed pointer heap) (localVar "raw")=some (.val (.word (pointer+62#64))):=by
    have cell : (beneficiaryStored hashed pointer heap).locals.lookup (ofString "raw")=some (.val (.word (pointer+62#64))):=frame2.raw
    simp [eval,evalHOLExact,toExact,localVar,cell]
  have third:=store_field_execute (beneficiaryStored hashed pointer heap) heap 32 (pointer+62#64+52#64)
    (Scalar.plus (localVar "raw") 52) output.environment.domain layout.headerArena layout.headerAligned (by decide) (by decide) frame2.header
    (Scalar.plus_read _ _ _ 52 rawRead2)
  exact ⟨frame2.stored source _ pointer record heap 32 _ layout.headerArena (by decide),secondTrace.command_known _ _ third⟩

def afterTransactionRoot : List CallPrefix.Action:=afterFixedHeader.drop 1
def allocatedTransactionRoot (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  let before:=stateRootStored hashed pointer heap
  setVarHOLFinite (ofString "txr") (.val (.word (afterOmmerHeap heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (afterOmmerHeap heap) 32#64)

set_option maxRecDepth 100000 in
theorem transaction_root_action : afterFixedHeader=
    .scoped (ofString "txr") .one (ofString "alloc") [.const 32#64]::afterTransactionRoot := by
  simp only [afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterTransactionRoot]
  rfl

/-- The next real allocation derives room for the transaction-root buffer;
the original header/input frame survives its genuine caller update. -/
theorem transaction_root_from_execution (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput source pointer record heap hashed)
    (execution : CallPrefix.Execution hashed afterOmmerHash current) :
    (afterOmmerHeap heap).toNat+32≤2952790016 ∧ AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧
      (afterOmmerHeap heap).toNat%8=0 ∧ (temporaryBase heap).toNat+8≤(afterOmmerHeap heap).toNat ∧
      HeaderFrame source (allocatedTransactionRoot hashed pointer heap) pointer record heap ∧
      CallPrefix.Execution (allocatedTransactionRoot hashed pointer heap) afterTransactionRoot current := by
  obtain ⟨frame,fixed⟩:=fixed_header_from_execution source hashed current pointer record heap layout output execution
  rw [transaction_root_action] at fixed
  have growth:=PersistentAlloc.guards (temporaryBase heap) 8#64 layout.temporaryRoom
  have args : evalListHOLFinite (stateRootStored hashed pointer heap)
      (h:=fun address=>Classical.propDecidable ((stateRootStored hashed pointer heap).memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next (source:=stateRootStored hashed pointer heap) (target:=current)
    (ofString "txr") [.const 32#64] (afterOmmerHeap heap) 32#64 afterTransactionRoot output.environment.installed args
    (output.heap source hashed pointer record heap) growth.2.2.2.1 fixed
  have previousLower:=layout.temporaryArena.lower
  have before:=growth.2.2.1
  change (temporaryBase heap).toNat+8≤(afterOmmerHeap heap).toNat at before
  exact ⟨room,⟨by omega,by omega⟩,growth.2.2.2.2,before,
    frame.allocated source _ pointer record heap (ofString "txr") _ _ (by decide) (by decide) (by decide) (by decide),next⟩

def wideZeroExpression : ExpHOL 64:=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]
def storeWideZero : ProgHOL 64:=.store (headerField 64) wideZeroExpression
def wideZeroStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  putHeader (putHeader (putHeader (putHeader source heap 64 0#64) heap 72 0#64) heap 80 0#64) heap 88 0#64

theorem wide_zero_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap))) :
    evaluateHOLFiniteState source storeWideZero=(none,wideZeroStored source heap) := by
  have address : eval source (headerField 64)=some (.val (.word (heap+64#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerField,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped (index : Fin 4) : source.memaddrs (heap+64#64+BitVec.ofNat 64 (8*index.val)):=by
    have cell:=AllocatedBytes.word_mapped source heap 248 (64+8*index.val) domain arena
      (by have inside:=index.isLt; omega) aligned (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using cell
  have run:=RlpWrite.U256Value.store_execute source (headerField 64) wideZeroExpression (heap+64#64) (fun _=>0#64) address rfl mapped
  simpa only [storeWideZero,wideZeroStored,putHeader,RlpWrite.U256Value.wordWrites,WordWrites.write,BitVec.add_assoc,
    show 64#64+8#64=72#64 from by decide,show 64#64+16#64=80#64 from by decide,show 64#64+24#64=88#64 from by decide] using run

theorem HeaderFrame.wide_zero (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap) (arena : AllocatedBytes.Arena heap 248) :
    HeaderFrame source (wideZeroStored current heap) pointer record heap := by
  have first:=frame.stored source current pointer record heap 64 0#64 arena (by decide)
  have second:=first.stored source _ pointer record heap 72 0#64 arena (by decide)
  have third:=second.stored source _ pointer record heap 80 0#64 arena (by decide)
  exact third.stored source _ pointer record heap 88 0#64 arena (by decide)

def payloadFieldActions (fields : List (Nat×Nat)) : List CallPrefix.Action:=
  fields.map (fun field=>.command (storeField field.1 (payloadField field.2)))
def payloadFieldsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record heap : BitVec 64)
    (current : PanSemStateFiniteExact 64 Guest.HostMemory) : List (Nat×Nat)→PanSemStateFiniteExact 64 Guest.HostMemory
  | []=>current
  | field::rest=>payloadFieldsStored source record heap (putHeader current heap field.1 (inputWord source record field.2)) rest

theorem payload_fields_from_execution {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat)
    (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (fields : List (Nat×Nat)) (tail : List CallPrefix.Action)
    (valid : ∀ field∈fields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0)
    (frame : HeaderFrame source current pointer record heap)
    (execution : CallPrefix.Execution current (payloadFieldActions fields++tail) target) :
    HeaderFrame source (payloadFieldsStored source record heap current fields) pointer record heap ∧
      CallPrefix.Execution (payloadFieldsStored source record heap current fields) tail target := by
  induction fields generalizing current with
  | nil=>exact ⟨frame,execution⟩
  | cons field rest ih=>
    obtain ⟨inside,fieldAligned,payloadInside,payloadAligned⟩:=valid field (by simp)
    have readValue:=frame.payload_read data before field.2 payloadInside payloadAligned
    have run:=store_field_execute current heap field.1 (inputWord source record field.2) (payloadField field.2)
      (frame.domain.trans data.arena.domain) arena aligned inside fieldAligned frame.header readValue
    have next:=execution.command_known _ _ run
    have nextFrame:=frame.stored source current pointer record heap field.1 (inputWord source record field.2) arena inside
    exact ih (current:=_) (by intro item member; exact valid item (List.mem_cons_of_mem _ member)) nextFrame next

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.fixed_header_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.fixed_header_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_root_action
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_root_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.wide_zero_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.wide_zero
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.payload_fields_from_execution
