import InitECandidate.Solver.Input.MainHashWorkspace
import InitECandidate.Solver.Input.SszHashProtected

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

/-- At the real main hash frontier, initializer provenance supplies the
current workspace; each mutable crypto buffer ends before copied input.
No preservation of input/decoded memory is assumed by this geometry. -/
theorem hashing_protected (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root query : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current)
    (afterInput : 2713731432≤query.toNat) :
    SszHash.Protected (RequestHash.entered current root) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 query :=
  ⟨hashing_ssz_workspace input before copiedSource current root copied actual,
    CopyGeneral.Away.before 2713714688#64 query 64 2713731432 (by decide) (by decide) afterInput,
    CopyGeneral.Away.before 2713714880#64 query 96 2713731432 (by decide) (by decide) afterInput,
    CopyGeneral.Away.before 2713715312#64 query 32 2713731432 (by decide) (by decide) afterInput⟩

theorem hashing_callee_protected (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root query : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current)
    (afterInput : 2713731432≤query.toNat) :
    SszHash.Protected (callEntryStateHOLFinite (RequestHash.entered current root) callee) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 query :=
  SszHash.Protected.at_callee _ callee _ _ _ _ _ (hashing_protected input before copiedSource current root query copied actual afterInput)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.hashing_protected
#print axioms InitECandidate.Solver.Input.Main.hashing_callee_protected
