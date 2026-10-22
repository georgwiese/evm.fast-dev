import InitECandidate.Solver.Input.PayloadHeaderFieldFacts

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main Main.RunAttemptConstructors

structure PhysicalHeader (input : Guest.InputBlob) (origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) : Prop where
  installed : OriginalCode.Installed current.code
  domain : current.memaddrs=InitE.ordinaryDomain
  little : current.be=false
  frame : HeaderFrame input source header current
  buffers : HeaderBuffers header
  frontier : HeapFrontier current header (headerFrontier header)
  rootBefore : root.toNat≤header.toNat
  inputFrame : HashInput.Frame origin current inputPointer.toNat root.toNat
  fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts current.memory header field
  optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts current.memory header field

/-- All physical encoder premises at the actual reached caller are
derived from main's decoder/initializer provenance and the executed
original prefix, without predicting any subsequent helper result. -/
theorem physical_header (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ header,PhysicalHeader input origin source current root header := by
  obtain ⟨header,hashed,words,heapCell,workspaceBefore,rootBefore,buffers,output,frame,frontier,same⟩:=
    complete_header_from_execution input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  have lower : 2713717616≤header.toNat:=by
    have low:=ready.rootLower
    change 2713731432≤root.toNat at low
    omega
  have cells (slot : Fin 31) : current.memory (header+BitVec.ofNat 64 (8*slot.val))=.word (headerWord input source header words slot):=by
    rw [same]
    exact complete_header_cells input source hashed header words buffers output lower slot
  obtain ⟨fields,optional⟩:=header_field_facts input origin source root header counts words prepared ready.inputFrame buffers current.memory cells
  have installed : OriginalCode.Installed current.code:=by rw [frame.code]; exact ready.state.1
  have domain:=frame.domain.trans ready.environment.domain
  have little:=frame.endian.trans (ready.little input origin initializer source root workspace nodes stateRoot codes)
  exact ⟨header,⟨installed,domain,little,frame,buffers,frontier,rootBefore,
    frame.input_frame input origin source current header root ready.inputFrame rootBefore,fields,optional⟩⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.physical_header
