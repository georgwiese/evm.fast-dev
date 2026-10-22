import InitECandidate.Solver.Input.PayloadHeaderFrame

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure HeapFrontier (current : PanSemStateFiniteExact 64 Guest.HostMemory) (header pointer : BitVec 64) : Prop where
  cell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer))
  arena : AllocatedBytes.Arena pointer 0
  aligned : pointer.toNat%8=0
  afterHeader : header.toNat+248≤pointer.toNat

def allocatedField (current : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (pointer amount : BitVec 64):=
  setVarHOLFinite name (.val (.word pointer)) (PersistentAlloc.post {current with clock:=current.clock-1} pointer amount)

theorem HeapFrontier.of_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header pointer : BitVec 64)
    (frontier : HeapFrontier source header pointer) (same : target.globals=source.globals) : HeapFrontier target header pointer :=
  ⟨by rw [same]; exact frontier.cell,frontier.arena,frontier.aligned,frontier.afterHeader⟩

/-- The true successful original allocation derives its complete fresh
extent and next frontier. No future room or allocation success is assumed. -/
theorem allocate_field (input : Guest.InputBlob) (source current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (header pointer amount : BitVec 64) (name : MlS) (rest : List CallPrefix.Action)
    (installed : OriginalCode.Installed source.code) (frame : HeaderFrame input source header current)
    (frontier : HeapFrontier current header pointer)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si")
    (execution : CallPrefix.Execution current (.scoped name .one (ofString "alloc") [.const amount]::rest) target) :
    AllocatedBytes.Arena pointer amount.toNat ∧
      HeaderFrame input source header (allocatedField current name pointer amount) ∧
      HeapFrontier (allocatedField current name pointer amount) header (PersistentAlloc.rounded pointer amount) ∧
      CallPrefix.Execution (allocatedField current name pointer amount) rest target := by
  have actualInstalled : OriginalCode.Installed current.code:=by rw [frame.code]; exact installed
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) [.const amount]=some (PersistentAlloc.values amount):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next name [.const amount] pointer amount rest actualInstalled args frontier.cell
    (by have h:=frontier.arena.upper; omega) execution
  have growth:=PersistentAlloc.guards pointer amount room
  have grows:=growth.2.2.1
  have before:=frontier.afterHeader
  have nextFrontier : HeapFrontier (allocatedField current name pointer amount) header (PersistentAlloc.rounded pointer amount):=by
    constructor
    · simp [allocatedField,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    · exact ⟨by have h:=frontier.arena.lower; omega,by have h:=growth.2.2.2.1; omega⟩
    · exact growth.2.2.2.2
    · omega
  exact ⟨⟨frontier.arena.lower,room⟩,frame.allocated input source current header name pointer amount notHeader notRaw notPayload notSI,nextFrontier,next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.allocate_field
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeapFrontier.of_globals
