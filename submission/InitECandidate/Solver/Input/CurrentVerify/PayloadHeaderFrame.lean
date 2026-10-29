import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderHash
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Live lexical bindings and the actual incoming memory during the header
prefix. Header contents and the advancing heap are tracked separately. -/
structure HeaderFrame (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) : Prop where
  code : current.code=source.code
  domain : current.memaddrs=source.memaddrs
  endian : current.be=source.be
  globals : ∀ key,key≠ofString "heap_ptr"→current.globals.lookup key=source.globals.lookup key
  header : current.locals.lookup (ofString "h")=some (.val (.word heap))
  raw : current.locals.lookup (ofString "raw")=some (.val (.word (pointer+62#64)))
  payload : current.locals.lookup (ofString "pl")=some (.val (.word record))
  si : current.locals.lookup (ofString "si")=source.locals.lookup (ofString "si")
  older : ∀ query,2701134824≤query.toNat→query.toNat<heap.toNat→current.memory query=source.memory query

theorem OmmerHashOutput.header_local (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (output : OmmerHashOutput source pointer record heap target) :
    target.locals.lookup (ofString "h")=some (.val (.word heap)) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,firstStored,putHeader,clearedHeader,headerEntry,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "h" from by decide,show ofString "oh"≠ofString "h" from by decide]

theorem OmmerHashOutput.raw_local (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (output : OmmerHashOutput source pointer record heap target) :
    target.locals.lookup (ofString "raw")=some (.val (.word (pointer+62#64))) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,firstStored,putHeader,clearedHeader,headerEntry,readEntry,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "raw" from by decide,show ofString "oh"≠ofString "raw" from by decide,
    show ofString "h"≠ofString "raw" from by decide]

theorem OmmerHashOutput.payload_local (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (output : OmmerHashOutput source pointer record heap target) :
    target.locals.lookup (ofString "pl")=some (.val (.word record)) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,firstStored,putHeader,clearedHeader,headerEntry,readEntry,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "pl" from by decide,show ofString "oh"≠ofString "pl" from by decide,
    show ofString "h"≠ofString "pl" from by decide,show ofString "raw"≠ofString "pl" from by decide]

theorem HeaderFrame.of_ommer (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput source pointer record heap hashed) :
    HeaderFrame source hashed pointer record heap := by
  have fields:=evaluation_fields (markedOmmer source pointer record heap) hashed hashOmmer none output.normal
  have si : hashed.locals.lookup (ofString "si")=source.locals.lookup (ofString "si"):=by
    rw [output.locals]
    simp [markedOmmer,temporaryAllocated,ommerAllocated,firstStored,putHeader,clearedHeader,headerEntry,readEntry,QueryBranch.bind,
      PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "tmp"≠ofString "si" from by decide,show ofString "oh"≠ofString "si" from by decide,
      show ofString "h"≠ofString "si" from by decide,show ofString "raw"≠ofString "si" from by decide,
      show ofString "pl"≠ofString "si" from by decide]
  exact ⟨fields.2.2.2,fields.1,fields.2.1,
    fun key other=>(output.globals key).trans (marked_ommer_globals source pointer record heap key other),
    output.header_local source hashed pointer record heap,output.raw_local source hashed pointer record heap,
    output.payload_local source hashed pointer record heap,si,
    fun query lower before=>output.older source hashed pointer record heap query layout lower before⟩

def storeField (offset : Nat) (value : ExpHOL 64) : ProgHOL 64:=.store (headerField offset) value

theorem store_field_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (offset : Nat) (value : BitVec 64) (expression : ExpHOL 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (inside : offset<248) (offsetAligned : offset%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap)))
    (readValue : eval source expression=some (.val (.word value))) :
    evaluateHOLFiniteState source (storeField offset expression)=(none,putHeader source heap offset value) := by
  have address : eval source (headerField offset)=some (.val (.word (heap+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerField,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact StoreWord.execute source (headerField offset) expression _ value address readValue
    (AllocatedBytes.word_mapped source heap 248 offset domain arena inside aligned offsetAligned)

theorem stored_field_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap query : BitVec 64)
    (offset : Nat) (value : BitVec 64) (arena : AllocatedBytes.Arena heap 248) (inside : offset<248)
    (before : query.toNat<heap.toNat) : (putHeader source heap offset value).memory query=source.memory query := by
  apply if_neg
  intro same
  have number:=byteAddress_toNat heap offset (by have upper:=arena.upper; omega)
  change (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset at number
  have numeric:=congrArg BitVec.toNat same
  omega

theorem HeaderFrame.stored (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap) (offset : Nat) (value : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (inside : offset<248) : HeaderFrame source (putHeader current heap offset value) pointer record heap :=
  ⟨frame.code,frame.domain,frame.endian,frame.globals,frame.header,frame.raw,frame.payload,frame.si,
    fun query lower before=>(stored_field_older current heap query offset value arena inside before).trans (frame.older query lower before)⟩

theorem HeaderFrame.allocated (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap) (name : MlS) (cursor amount : BitVec 64)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si") :
    HeaderFrame source (setVarHOLFinite name (.val (.word cursor))
      (PersistentAlloc.post {current with clock:=current.clock-1} cursor amount)) pointer record heap := by
  refine ⟨frame.code,frame.domain,frame.endian,?_,?_,?_,?_,?_,frame.older⟩
  · intro key other
    change (current.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor amount)))).lookup key=_
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm other] using frame.globals key other
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notHeader] using frame.header
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notRaw] using frame.raw
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notPayload] using frame.payload
  · simpa [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notSI] using frame.si

theorem HeaderFrame.of_memory_clock (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap) (memory : WordWrites.Memory) (clock : Nat)
    (older : ∀ query,2701134824≤query.toNat→query.toNat<heap.toNat→memory query=current.memory query) :
    HeaderFrame source {current with memory:=memory,clock:=clock} pointer record heap :=
  ⟨frame.code,frame.domain,frame.endian,frame.globals,frame.header,frame.raw,frame.payload,frame.si,
    fun query lower before=>(older query lower before).trans (frame.older query lower before)⟩

theorem HeaderFrame.declared (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap) (name : MlS) (value : ValueHOL 64)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si") :
    HeaderFrame source (setVarHOLFinite name value current) pointer record heap := by
  refine ⟨frame.code,frame.domain,frame.endian,frame.globals,?_,?_,?_,?_,frame.older⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notHeader] using frame.header
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notRaw] using frame.raw
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notPayload] using frame.payload
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notSI] using frame.si

theorem HeaderFrame.environment (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (frame : HeaderFrame source current pointer record heap)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64) :
    CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64 :=
  ⟨by rw [frame.code]; exact environment.installed,frame.domain.trans environment.domain,
    (frame.globals _ (by decide)).trans environment.stateGlobal,(frame.globals _ (by decide)).trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

def inputWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (offset : Nat) : BitVec 64:=
  MemoryBytes.wordBits (source.memory (record+BitVec.ofNat 64 offset))
def payloadField (offset : Nat) : ExpHOL 64:=.load .one (Scalar.plus (localVar "pl") offset)

/-- Each real scalar payload read is derived from the retained incoming
record, not supplied as a later read-success hypothesis. -/
theorem HeaderFrame.payload_read {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (frame : HeaderFrame source current pointer record heap) (data : Data input source pointer si record gasWord boundary)
    (before : boundary≤heap.toNat) (offset : Nat) (inside : offset<136) (aligned : offset%8=0) :
    eval current (payloadField offset)=some (.val (.word (inputWord source record offset))) := by
  have number:=byteAddress_toNat record offset (by have upper:=data.recordArena.upper; omega)
  change (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset at number
  have same:=frame.older (record+BitVec.ofNat 64 offset)
    (by rw [number]; have lower:=data.recordInside.1; omega)
    (by rw [number]; have extent:=data.recordInside.2; omega)
  have stored : source.memory (record+BitVec.ofNat 64 offset)=.word (inputWord source record offset):=by
    cases cell:source.memory (record+BitVec.ofNat 64 offset) with
    | word value=>simp [inputWord,cell,MemoryBytes.wordBits]
  have plRead : eval current (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,localVar,frame.payload]
  exact Witness.load_word_read current (Scalar.plus (localVar "pl") offset) (record+BitVec.ofNat 64 offset) (inputWord source record offset)
    (Scalar.plus_read current (localVar "pl") record offset plRead)
    (AllocatedBytes.word_mapped current record 136 offset (frame.domain.trans data.arena.domain) data.recordArena inside data.recordAligned aligned)
    (same.trans stored)

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.header_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.raw_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.payload_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.of_ommer
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.store_field_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.stored_field_older
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.stored
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.allocated
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.of_memory_clock
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.declared
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.payload_read
