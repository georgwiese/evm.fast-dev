import InitECandidate.Solver.Input.PayloadHeaderTransactionRootAllocation

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

/-- Live input/header bindings and the old persistent memory during the
original header prefix. The frontier and header contents are tracked separately. -/
structure HeaderFrame (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  code : current.code=source.code
  domain : current.memaddrs=source.memaddrs
  endian : current.be=source.be
  oracle : current.ffi.oracle=source.ffi.oracle
  globals : HeapGlobals source current
  header : current.locals.lookup (ofString "h")=some (.val (.word heap))
  raw : current.locals.lookup (ofString "raw")=some (.val (.word (inputPointer+62#64)))
  payload : current.locals.lookup (ofString "pl")=some (.val (.word (PayloadPrefix.cursor input)))
  si : current.locals.lookup (ofString "si")=source.locals.lookup (ofString "si")
  older : ∀ query,2713717616≤query.toNat→query.toNat<heap.toNat→current.memory query=source.memory query

theorem HeaderFrame.of_ommer (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap hashed) :
    HeaderFrame input source heap hashed := by
  have code:=congrArg PanSemStateFiniteExact.code output.control
  have domain:=congrArg PanSemStateFiniteExact.memaddrs output.control
  have endian:=congrArg PanSemStateFiniteExact.be output.control
  have oracle:=congrArg (fun state=>state.ffi.oracle) output.control
  have si : hashed.locals.lookup (ofString "si")=source.locals.lookup (ofString "si"):=by
    rw [output.locals]
    simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,
      readEntry,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "tmp"≠ofString "si" from by decide,show ofString "oh"≠ofString "si" from by decide,
      show ofString "h"≠ofString "si" from by decide,show ofString "raw"≠ofString "si" from by decide,
      show ofString "pl"≠ofString "si" from by decide]
  refine ⟨code,domain,endian,oracle,?_,output.header_local input source hashed heap,
    output.raw_local input source hashed heap,output.payload_local input source hashed heap,si,
    (fun query lower before=>output.older input source hashed heap query layout lower before)⟩
  intro key other
  have globals:=congrArg (fun state=>state.globals.lookup key) output.control
  change hashed.globals.lookup key=(markedOmmer input source heap).globals.lookup key at globals
  rw [globals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,
    readEntry,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

theorem HeaderFrame.stored (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (offset : Nat) (value : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (inside : offset<248) :
    HeaderFrame input source heap (storedField current heap offset value) := by
  refine ⟨frame.code,frame.domain,frame.endian,frame.oracle,frame.globals,frame.header,frame.raw,frame.payload,frame.si,?_⟩
  intro query lower before
  exact (stored_field_older current heap query offset value arena inside before).trans (frame.older query lower before)

theorem HeaderFrame.allocated (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (name : MlS) (pointer amount : BitVec 64)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si") :
    HeaderFrame input source heap (setVarHOLFinite name (.val (.word pointer))
      (PersistentAlloc.post {current with clock:=current.clock-1} pointer amount)) := by
  refine ⟨frame.code,frame.domain,frame.endian,frame.oracle,?_,?_,?_,?_,?_,frame.older⟩
  · intro key other
    change (current.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded pointer amount)))).lookup key=_
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm other] using frame.globals key other
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notHeader] using frame.header
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notRaw] using frame.raw
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notPayload] using frame.payload
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notSI] using frame.si

theorem HeaderFrame.of_memory_clock (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (memory : WordWrites.Memory) (clock : Nat)
    (older : ∀ query,2713717616≤query.toNat→query.toNat<heap.toNat→memory query=current.memory query) :
    HeaderFrame input source heap {current with memory:=memory,clock:=clock} :=
  ⟨frame.code,frame.domain,frame.endian,frame.oracle,frame.globals,frame.header,frame.raw,frame.payload,frame.si,
    fun query lower before=>(older query lower before).trans (frame.older query lower before)⟩

theorem HeaderFrame.declared (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (name : MlS) (value : ValueHOL 64)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si") :
    HeaderFrame input source heap (setVarHOLFinite name value current) := by
  refine ⟨frame.code,frame.domain,frame.endian,frame.oracle,frame.globals,?_,?_,?_,?_,frame.older⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notHeader] using frame.header
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notRaw] using frame.raw
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notPayload] using frame.payload
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notSI] using frame.si

theorem HeaderFrame.environment (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    Keccak256.Environment current 2713714976#64 2713715176#64 :=
  Keccak256.Environment.of_fields source current _ _ environment frame.domain frame.code frame.oracle frame.globals

theorem HeaderFrame.transaction_root (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap hashed) :
    HeaderFrame input source heap (allocatedTransactionRoot hashed heap) := by
  have frame:=HeaderFrame.of_ommer input source hashed heap layout output
  have first:=frame.stored input source hashed heap 16 (ommerBase heap) layout.headerArena (by decide)
  have second:=first.stored input source (ommerStored hashed heap) heap 24 (inputPointer+62#64+32#64) layout.headerArena (by decide)
  have third:=second.stored input source (beneficiaryStored hashed heap) heap 32 (inputPointer+62#64+52#64) layout.headerArena (by decide)
  exact third.allocated input source (stateRootStored hashed heap) heap (ofString "txr") (afterOmmerHeap heap) 32#64
    (by decide) (by decide) (by decide) (by decide)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.of_ommer
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.stored
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.allocated
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.of_memory_clock
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.declared
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.environment
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.transaction_root
