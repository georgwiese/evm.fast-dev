import InitECandidate.Solver.Input.MainRequestRootHashBudget
import InitECandidate.Solver.Input.MainHashWorkspace

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current main caller facts derived from original startup/copy/decoder
provenance and its real root allocation. No later hash outcome is included. -/
structure Prepared (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64) : Prop where
  image : (description input counts).Image current
  layout : (description input counts).Layout inputPointer.toNat root.toNat (input.length%2^64)
  geometry : (description input counts).RuntimeGeometry (input.length%2^64) (PersistentAlloc.rounded root 32#64)
  output : PayloadHash.FinalPhase.OutputGeometry root root.toNat
  workspace : SszHash.Workspace (RequestHash.entered current root) 2713714688#64 2713714880#64 2713715312#64 2713715408#64
  frame : HashInput.Frame current (RequestHash.entered current root) inputPointer.toNat root.toNat
  heap : (RequestHash.entered current root).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded root 32#64)))
  before : root.toNat≤(PersistentAlloc.rounded root 32#64).toNat
  arguments : evalListHOLFinite (RequestHash.entered current root) (h:=fun address=>Classical.propDecidable ((RequestHash.entered current root).memaddrs address)) RequestHash.arguments=
    some (RequestRootHash.values (description input counts).si root)
  budget : dataBytes (description input counts)+DecoderCall.witnessLength input≤input.length%2^64

/-- The same actual copied/decoded main execution supplies every premise of
the complete original request-root caller contract and its shared budget. -/
theorem prepared (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current)
    (bounded : input.length%2^64≤Guest.maxInputBytes) (heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word root))) :
    ∃ counts : Nat→BitVec 64,Prepared input current root counts := by
  obtain ⟨counts,requestLayout,requestImage,shared⟩ := budget input (DecoderSetup.entered copiedSource input) current actual
  have context := DecoderSetup.entered_context copiedSource input
  have callerDomain : (DecoderSetup.entered copiedSource input).memaddrs=copiedSource.memaddrs := by
    have h:=congrArg PanSemStateFiniteExact.memaddrs context
    exact h
  have domain : current.memaddrs=InitE.ordinaryDomain := actual.domain.trans (callerDomain.trans copied.domain)
  obtain ⟨mapped,scratch,output,number⟩ := geometry input (DecoderSetup.entered copiedSource input) current counts root actual bounded heap requestLayout requestImage
  have fields := RequestHash.entered_fields input (DecoderSetup.entered copiedSource input) current root actual
  refine ⟨counts,{
    image := image input (DecoderSetup.entered copiedSource input) current counts actual domain requestImage
    layout := mapped
    geometry := scratch
    output := output
    workspace := hashing_ssz_workspace input before copiedSource current root copied actual
    frame := ⟨by intro query low high; rfl⟩
    heap := fields.2.2.2.2.1
    before := by rw [number]; omega
    arguments := RequestRootHash.main_arguments input (DecoderSetup.entered copiedSource input) current root actual
    budget := shared
  }⟩

theorem separation : HashInput.Separation 2713714688#64 2713714880#64 2713715312#64 inputPointer.toNat :=
  ⟨by decide,by decide,by decide⟩

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.prepared
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.separation
