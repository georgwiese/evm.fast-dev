import InitECandidate.Solver.Input.MainShaWorkspace
import InitECandidate.Solver.Input.SszHashWorkspace

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

/-- The original complete SSZ hash workspace is derived from retained
startup/copied-input/decoder provenance at the same actual main hash entry. -/
theorem hashing_ssz_workspace (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) :
    SszHash.Workspace (RequestHash.entered current root) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 :=
  ⟨hashing_workspace input before copiedSource current root copied actual,(CryptoWorkspace.Field.geometry .shaState).1,
    CryptoWorkspace.hashing_value input before copiedSource current root copied actual .lengthChunk,(CryptoWorkspace.Field.geometry .lengthChunk).1,(CryptoWorkspace.Field.geometry .lengthChunk).2.1,
    CryptoWorkspace.hashing_value input before copiedSource current root copied actual .zeroHashes,(CryptoWorkspace.Field.geometry .zeroHashes).1⟩

theorem hashing_callee_ssz_workspace (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) :
    SszHash.Workspace (callEntryStateHOLFinite (RequestHash.entered current root) callee) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 :=
  SszHash.Workspace.at_callee _ callee _ _ _ _ (hashing_ssz_workspace input before copiedSource current root copied actual)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.hashing_ssz_workspace
#print axioms InitECandidate.Solver.Input.Main.hashing_callee_ssz_workspace
