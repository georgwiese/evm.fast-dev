import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.PayloadHeaderEnvironment
import InitECandidate.Solver.Input.PayloadHeaderPrefixTrace
import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

abbrev actions := PayloadHeader.actions
abbrev lengthCall := PayloadHeader.lengthCall
def afterReads : List CallPrefix.Action:=actions.drop 2
def afterHeader : List CallPrefix.Action:=afterReads.drop 1
def field (name : String) : ExpHOL 64:=.load .one (.op .add [localVar name,.const 0#64])
def readEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record : BitVec 64):=
  bind (bind source "pl" record) "raw" (pointer+62#64)
def headerEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  bind (PersistentAlloc.post {(readEntry source pointer record) with clock:=source.clock-1} heap 248#64) "h" heap

set_option maxRecDepth 100000 in
theorem initial_actions : actions=.declare (ofString "pl") .one (field "si")::
    .declare (ofString "raw") .one (field "pl")::afterReads := by
  simp only [actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterReads,List.drop_cons,List.drop_zero,field,localVar]
  rfl

set_option maxRecDepth 100000 in
theorem first_allocation_action : afterReads=.scoped (ofString "h") .one (ofString "alloc") [.const 248#64]::afterHeader := by
  simp only [afterReads,afterHeader,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,List.drop_cons,List.drop_zero]
  rfl

/-- Real SI/payload reads expose the actual lexical pl/raw bindings.
Pointers refer to the same decoded input retained through current main. -/
theorem initial_scopes {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    CallPrefix.Execution (readEntry source pointer record) afterReads current := by
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by simp [eval,evalHOLExact,localVar,toExact,data.siLocal]
  have payloadRead : eval source (field "si")=some (.val (.word record)) :=
    Witness.load_word_read source (Scalar.plus (localVar "si") 0) (si+0#64) record
      (Scalar.plus_read source (localVar "si") si 0 siRead)
      (AllocatedBytes.word_mapped source si 96 0 data.arena.domain data.siArena (by decide) data.siAligned (by decide)) (by simpa using data.payloadCell)
  let next:=bind source "pl" record
  have plRead : eval next (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,localVar,toExact,show next.locals.lookup (ofString "pl")=some (.val (.word record)) from bind_lookup_same _ _ _]
  obtain ⟨array,length,start,size,payload,before,count,bytes⟩:=data.payload
  have rawRead : eval next (field "pl")=some (.val (.word (pointer+62#64))) :=
    Witness.load_word_read next (Scalar.plus (localVar "pl") 0) (record+0#64) (pointer+62#64)
      (Scalar.plus_read next (localVar "pl") record 0 plRead)
      (AllocatedBytes.word_mapped next record 136 0 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide))
      (by simpa [next,QueryBranch.bind,setVarHOLFinite] using payload.transactions.hashPrefix.raw)
  rw [initial_actions] at execution
  exact (execution.declare_next (.val (.word record)) payloadRead).declare_next (.val (.word (pointer+62#64))) rawRead

/-- The genuine first allocation derives its own248-byte request room,
real header address and complete normal persistent frame. Later prefix
allocations and output reads are not assumed successful. -/
theorem first_allocation {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ heap.toNat+248≤2952790016 ∧
      AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧ boundary+32≤heap.toNat ∧
      PersistentNormalFrame source (headerEntry source pointer record heap) heap ∧
      CallPrefix.Execution (headerEntry source pointer record heap) afterHeader current := by
  have scopes:=initial_scopes data execution
  rw [first_allocation_action] at scopes
  obtain ⟨heap,heapCell,heapLower,heapUpper,heapAligned⟩:=data.heap
  obtain ⟨room,continued⟩:=CallPrefix.Execution.alloc_next (source:=readEntry source pointer record) (target:=current)
    (ofString "h") [.const 248#64] heap 248#64 afterHeader data.arena.code rfl heapCell heapUpper scopes
  have heapArena : AllocatedBytes.Arena heap 0:=⟨by have lower:=data.recordInside.1; have extent:=data.recordInside.2; omega,by omega⟩
  have frame:=PersistentAlloc.post_persistent_frame {(readEntry source pointer record) with clock:=source.clock-1} heap 248#64 heapArena room
  have actual : PersistentNormalFrame source (headerEntry source pointer record heap) heap:=frame.of_erase _ _ source _ heap rfl rfl
  exact ⟨heap,heapCell,room,⟨heapArena.lower,by change heap.toNat+248≤2952790016 at room; omega⟩,heapAligned,heapLower,actual,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.initial_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_allocation_action
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.initial_scopes
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_allocation
