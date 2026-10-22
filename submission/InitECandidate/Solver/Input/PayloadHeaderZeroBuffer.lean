import InitECandidate.Solver.Input.PayloadHeaderZeroAllocation

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def zeroBufferCall : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "z8",.const 8#64]
def afterZeroBuffer : List CallPrefix.Action:=afterZeroAllocation.drop 2
def clearedZero (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let allocated:=allocatedZero input source hashed heap
  {allocated with memory:=Zero.finalMemory allocated.memory (zeroBase heap) 8,clock:=allocated.clock-(Zero.price 8+1)}
def zeroPointerStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (clearedZero input source hashed heap) heap 152 (zeroBase heap)

set_option maxRecDepth 100000 in
theorem zero_buffer_actions : afterZeroAllocation=
    .command zeroBufferCall::.command (storeField 152 (localVar "z8"))::afterZeroBuffer := by
  simp only [afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,
    afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterZeroBuffer,zeroBufferCall,storeField,headerAddress,localVar]
  rfl

theorem zero_buffer_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (layout : OmmerLayout heap) (arena : AllocatedBytes.Arena (zeroBase heap) 8) (aligned : (zeroBase heap).toNat%8=0)
    (before : heap.toNat≤(zeroBase heap).toNat) (frame : HeaderFrame input source heap (allocatedZero input source hashed heap))
    (execution : CallPrefix.Execution (allocatedZero input source hashed heap) afterZeroAllocation current) :
    HeaderFrame input source heap (zeroPointerStored input source hashed heap) ∧
      CallPrefix.Execution (zeroPointerStored input source hashed heap) afterZeroBuffer current := by
  rw [zero_buffer_actions] at execution
  obtain ⟨middle,normal,next⟩:=execution.command_next zeroBufferCall _
  let allocated:=allocatedZero input source hashed heap
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
  change middle=clearedZero input source hashed heap at same
  rw [same] at next
  have clearedFrame : HeaderFrame input source heap (clearedZero input source hashed heap):=by
    apply HeaderFrame.of_memory_clock input source (allocatedZero input source hashed heap) heap frame
    intro query lower high
    apply Zero.final_memory_away
    intro offset inside equal
    have number:=byteAddress_toNat (zeroBase heap) offset (by have h:=arena.upper; omega)
    have numeric:=congrArg BitVec.toNat equal
    omega
  have run:=store_field_execute (clearedZero input source hashed heap) heap 152 (zeroBase heap) (localVar "z8")
    (clearedFrame.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) clearedFrame.header
    (Request.local_word _ "z8" _ z8Cell)
  exact ⟨clearedFrame.stored input source _ heap 152 _ layout.headerArena (by decide),next.command_known _ _ run⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.zero_buffer_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.zero_buffer_from_execution
