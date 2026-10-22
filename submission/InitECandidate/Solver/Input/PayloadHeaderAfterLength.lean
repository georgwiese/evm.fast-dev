import InitECandidate.Solver.Input.PayloadHeaderLengthCallNormal
import InitECandidate.Solver.Input.HeaderEncoding.FieldFrame

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main

/-- The actual block-length child releases its temporary allocation. Its
real caller continuation retains the complete physical header, input and
heap frontier, while binding the computed length in bl. -/
theorem PhysicalHeader.after_length (input : Guest.InputBlob) (origin source current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (physical : PhysicalHeader input origin source current root header) (value : ValueHOL 64)
    (control : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {current with memory:=target.memory,clock:=target.clock})
    (old : HeaderEncoding.OldMemory target.memory current.memory (headerFrontier header)) :
    PhysicalHeader input origin source (CallNormal.continuationEntry current target "bl" value) root header := by
  let continued:=CallNormal.continuationEntry current target "bl" value
  have rootBefore:=physical.rootBefore
  have headerBefore:=physical.frontier.afterHeader
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=current.locals}) control
  change {target with locals:=current.locals}={current with memory:=target.memory,clock:=target.clock} at restored
  have continuedEq : continued=setVarHOLFinite (ofString "bl") value {current with memory:=target.memory,clock:=target.clock}:=
    congrArg (setVarHOLFinite (ofString "bl") value) restored
  have frame:=physical.frame.of_memory_clock input source current header target.memory target.clock
    (by intro query lower before; exact old query (by omega))
  have continuedFrame : HeaderFrame input source header continued:=by
    rw [continuedEq]
    exact frame.declared input source _ header (ofString "bl") value (by decide) (by decide) (by decide) (by decide)
  have code:=congrArg PanSemStateFiniteExact.code control
  change target.code=current.code at code
  have domain:=congrArg PanSemStateFiniteExact.memaddrs control
  have endian:=congrArg PanSemStateFiniteExact.be control
  have globals:=congrArg PanSemStateFiniteExact.globals control
  have installed : OriginalCode.Installed continued.code:=by
    change OriginalCode.Installed target.code
    rw [code]
    exact physical.installed
  have cells (offset : Nat) (inside : offset≤240) :
      target.memory (HeaderEncoding.address header offset)=current.memory (HeaderEncoding.address header offset):=by
    apply old
    have number:=byteAddress_toNat header offset (by have h:=physical.buffers.ommer.headerArena.upper; omega)
    change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at number
    change (header+BitVec.ofNat 64 offset).toNat<(headerFrontier header).toNat
    omega
  refine ⟨installed,domain.trans physical.domain,endian.trans physical.little,continuedFrame,physical.buffers,
    physical.outputs.after_length current target header value,
    physical.frontier.of_globals current continued header (headerFrontier header) globals,rootBefore,?_,?_,?_⟩
  · constructor
    intro query low high
    exact (old query (by omega)).trans (physical.inputFrame.words query low high)
  · intro field member
    exact HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.fields field member)
  · intro field member
    exact HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.optional field member)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.PhysicalHeader.after_length
