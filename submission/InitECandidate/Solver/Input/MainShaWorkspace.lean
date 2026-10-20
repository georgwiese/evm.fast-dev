import InitECandidate.Solver.Input.MainCryptoWorkspace
import InitECandidate.Solver.Input.ShaWorkspace

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

/-- The reusable SHA runtime workspace is derived at the same actual main
hashing entry, using original initialization provenance and decoded state. -/
theorem hashing_workspace (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) :
    ShaPair.Workspace (RequestHash.entered current root) 2713714688#64 2713714880#64 := by
  have context := DecoderSetup.entered_context copiedSource input
  have setupCode : (DecoderSetup.entered copiedSource input).code=copiedSource.code := by have h := congrArg PanSemStateFiniteExact.code context; exact h
  have setupDomain : (DecoderSetup.entered copiedSource input).memaddrs=copiedSource.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs context; exact h
  have code : (RequestHash.entered current root).code=copiedSource.code := actual.code.trans setupCode
  have domain : (RequestHash.entered current root).memaddrs=InitE.ordinaryDomain := actual.domain.trans (setupDomain.trans copied.domain)
  have state := CryptoWorkspace.hashing_value input before copiedSource current root copied actual .shaState
  have accelerator := CryptoWorkspace.hashing_value input before copiedSource current root copied actual .shaAccel
  have geometry := CryptoWorkspace.Field.geometry .shaAccel
  exact ⟨code.symm ▸ copied.code,domain,state,accelerator,geometry.1,geometry.2.1⟩

theorem hashing_callee_workspace (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) :
    ShaPair.Workspace (callEntryStateHOLFinite (RequestHash.entered current root) callee) 2713714688#64 2713714880#64 :=
  ShaPair.Workspace.at_callee _ callee _ _ (hashing_workspace input before copiedSource current root copied actual)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.hashing_workspace
#print axioms InitECandidate.Solver.Input.Main.hashing_callee_workspace
