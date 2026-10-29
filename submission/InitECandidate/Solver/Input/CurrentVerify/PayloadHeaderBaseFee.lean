import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderZero
import InitECandidate.Solver.Input.CallPrefixCheckedDeclaration

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def zeroBufferCall : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "z8",.const 8#64]
def afterZeroBuffer : List CallPrefix.Action:=afterZeroAllocation.drop 2
def clearedZero (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  let allocated:=allocatedZero source hashed pointer record heap
  {allocated with memory:=Zero.finalMemory allocated.memory (zeroBase heap) 8,clock:=allocated.clock-(Zero.price 8+1)}
def zeroPointerStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  putHeader (clearedZero source hashed pointer record heap) heap 152 (zeroBase heap)

set_option maxRecDepth 100000 in
theorem zero_buffer_actions : afterZeroAllocation=
    .command zeroBufferCall::.command (storeField 152 (localVar "z8"))::afterZeroBuffer := by
  simp only [afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,
    afterFirstStores,afterClear,afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterZeroBuffer,zeroBufferCall,storeField,headerField,localVar]
  rfl

theorem zero_buffer_from_execution (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (layout : OmmerLayout heap) (arena : AllocatedBytes.Arena (zeroBase heap) 8) (aligned : (zeroBase heap).toNat%8=0)
    (before : heap.toNat≤(zeroBase heap).toNat) (frame : HeaderFrame source (allocatedZero source hashed pointer record heap) pointer record heap)
    (execution : CallPrefix.Execution (allocatedZero source hashed pointer record heap) afterZeroAllocation current) :
    HeaderFrame source (zeroPointerStored source hashed pointer record heap) pointer record heap ∧
      CallPrefix.Execution (zeroPointerStored source hashed pointer record heap) afterZeroBuffer current := by
  rw [zero_buffer_actions] at execution
  obtain ⟨middle,normal,next⟩:=execution.command_next zeroBufferCall _
  let allocated:=allocatedZero source hashed pointer record heap
  have z8Cell : allocated.locals.lookup (ofString "z8")=some (.val (.word (zeroBase heap))):=bind_lookup_same _ _ _
  have args : evalListHOLFinite allocated (h:=fun address=>Classical.propDecidable (allocated.memaddrs address))
      [localVar "z8",.const 8#64]=some (Zero.values (zeroBase heap) 8):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,z8Cell,Zero.values]
  have actualCode : allocated.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one):=by
    rw [frame.code]
    exact Zero.original_code source.code installed
  have mapped (offset : Nat) (inside : offset+8≤8) (multiple : offset%8=0) : allocated.memaddrs (byteAddress (zeroBase heap) offset):=
    AllocatedBytes.word_mapped allocated (zeroBase heap) 8 offset (frame.domain.trans domain) arena (by omega) aligned multiple
  obtain ⟨funded,same⟩:=Zero.call_normal allocated middle [localVar "z8",.const 8#64] (zeroBase heap) 8 args actualCode
    (by decide) (by decide) aligned mapped normal
  change middle=clearedZero source hashed pointer record heap at same
  rw [same] at next
  have clearedFrame : HeaderFrame source (clearedZero source hashed pointer record heap) pointer record heap:=by
    apply HeaderFrame.of_memory_clock source (allocatedZero source hashed pointer record heap) pointer record heap frame
    intro query lower high
    apply Zero.final_memory_away
    intro offset inside equal
    have number:=byteAddress_toNat (zeroBase heap) offset (by have upper:=arena.upper; omega)
    have numeric:=congrArg BitVec.toNat equal
    omega
  have run:=store_field_execute (clearedZero source hashed pointer record heap) heap 152 (zeroBase heap) (localVar "z8")
    (clearedFrame.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) clearedFrame.header
    (local_word_read _ "z8" _ z8Cell)
  exact ⟨clearedFrame.stored source _ pointer record heap 152 _ layout.headerArena (by decide),next.command_known _ _ run⟩

def wideStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (words : RlpWrite.U256Value.Words):=
  putHeader (putHeader (putHeader (putHeader source heap offset (words 0))
    heap (offset+8) (words 1)) heap (offset+16) (words 2)) heap (offset+24) (words 3)

theorem store_wide_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (offset : Nat) (words : RlpWrite.U256Value.Words) (expression : ExpHOL 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (inside : offset+32≤248) (offsetAligned : offset%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap)))
    (readValue : eval source expression=some (RlpWrite.U256Value.tuple words)) :
    evaluateHOLFiniteState source (.store (headerField offset) expression)=(none,wideStored source heap offset words) := by
  have address : eval source (headerField offset)=some (.val (.word (heap+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerField,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped (index : Fin 4) : source.memaddrs (heap+BitVec.ofNat 64 offset+BitVec.ofNat 64 (8*index.val)):=by
    have cell:=AllocatedBytes.word_mapped source heap 248 (offset+8*index.val) domain arena
      (by have bound:=index.isLt; omega) aligned (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using cell
  have run:=RlpWrite.U256Value.store_execute source (headerField offset) expression _ words address readValue mapped
  simpa only [wideStored,putHeader,RlpWrite.U256Value.wordWrites,WordWrites.write,BitVec.ofNat_add,BitVec.add_assoc] using run

theorem HeaderFrame.wide_stored (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (frame : HeaderFrame source current pointer record heap) (offset : Nat) (words : RlpWrite.U256Value.Words)
    (arena : AllocatedBytes.Arena heap 248) (inside : offset+32≤248) : HeaderFrame source (wideStored current heap offset words) pointer record heap := by
  have first:=frame.stored source current pointer record heap offset (words 0) arena (by omega)
  have second:=first.stored source _ pointer record heap (offset+8) (words 1) arena (by omega)
  have third:=second.stored source _ pointer record heap (offset+16) (words 2) arena (by omega)
  exact third.stored source _ pointer record heap (offset+24) (words 3) arena (by omega)

def baseFeeExpression : ExpHOL 64:=match afterZeroBuffer with | .declare _ _ expression::_=>expression | _=>.const 0#64
def afterBaseFee : List CallPrefix.Action:=afterZeroBuffer.drop 2
def feeEntry (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  setVarHOLFinite (ofString "bf") (RlpWrite.U256Value.tuple words) (zeroPointerStored source hashed pointer record heap)
def baseFeeStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  wideStored (feeEntry source hashed pointer record heap words) heap 160 words

set_option maxRecDepth 100000 in
theorem base_fee_actions : afterZeroBuffer=
    .declare (ofString "bf") RlpWrite.U256Value.tupleShape baseFeeExpression::
    .command (.store (headerField 160) (localVar "bf"))::afterBaseFee := by
  simp only [afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,
    afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterBaseFee,baseFeeExpression,RlpWrite.U256Value.tupleShape,headerField,localVar]
  rfl

/-- The real checked four-word declaration supplies its returned base fee.
A failed earlier byte read is covered by the existing all-outcome prefix bound. -/
theorem base_fee_from_execution (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (layout : OmmerLayout heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (frame : HeaderFrame source (zeroPointerStored source hashed pointer record heap) pointer record heap)
    (execution : CallPrefix.Execution (zeroPointerStored source hashed pointer record heap) afterZeroBuffer current) :
    ∃ words : RlpWrite.U256Value.Words,
      eval (zeroPointerStored source hashed pointer record heap) baseFeeExpression=some (RlpWrite.U256Value.tuple words) ∧
      HeaderFrame source (baseFeeStored source hashed pointer record heap words) pointer record heap ∧
      CallPrefix.Execution (baseFeeStored source hashed pointer record heap words) afterBaseFee current := by
  rw [base_fee_actions] at execution
  obtain ⟨words,read,next⟩:=execution.declare_words
  have feeFrame:=frame.declared source _ pointer record heap (ofString "bf") (RlpWrite.U256Value.tuple words)
    (by decide) (by decide) (by decide) (by decide)
  have value : eval (feeEntry source hashed pointer record heap words) (localVar "bf")=some (RlpWrite.U256Value.tuple words):=by
    simp [eval,evalHOLExact,toExact,localVar,feeEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have run:=store_wide_execute (feeEntry source hashed pointer record heap words) heap 160 words (localVar "bf")
    (feeFrame.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) feeFrame.header value
  exact ⟨words,read,feeFrame.wide_stored source _ pointer record heap 160 words layout.headerArena (by decide),next.command_known _ _ run⟩

def withdrawalBase (heap : BitVec 64):=PersistentAlloc.rounded (zeroBase heap) 8#64

/-- Main reaches the genuine base-fee store with all earlier decoded data
protected and its actual next bounded heap retained. -/
theorem base_fee_reached {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,∃ words : RlpWrite.U256Value.Words,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ boundary+32≤heap.toNat ∧
      OmmerLayout heap ∧ OmmerHashOutput source pointer record heap hashed ∧
      AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧ AllocatedBytes.Arena (zeroBase heap) 8 ∧
      HeaderFrame source (baseFeeStored source hashed pointer record heap words) pointer record heap ∧
      HeapFrontier (baseFeeStored source hashed pointer record heap words) heap (withdrawalBase heap) ∧
      CallPrefix.Execution (baseFeeStored source hashed pointer record heap words) afterBaseFee current := by
  obtain ⟨heap,hashed,cell,before,layout,output,txArena,zeroArena,zeroAligned,zeroBefore,zeroFrame,frontier,zeroTrace⟩:=zero_allocation data execution
  obtain ⟨clearedFrame,clearedTrace⟩:=zero_buffer_from_execution source hashed current pointer record heap data.arena.code data.arena.domain
    layout zeroArena zeroAligned (by omega) zeroFrame zeroTrace
  obtain ⟨words,read,feeFrame,feeTrace⟩:=base_fee_from_execution source hashed current pointer record heap layout data.arena.domain clearedFrame clearedTrace
  exact ⟨heap,hashed,words,cell,before,layout,output,txArena,zeroArena,feeFrame,
    frontier.of_globals _ (baseFeeStored source hashed pointer record heap words) heap _ rfl,feeTrace⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.zero_buffer_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.zero_buffer_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.store_wide_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.wide_stored
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.base_fee_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.base_fee_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.base_fee_reached
