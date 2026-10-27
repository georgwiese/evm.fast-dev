import InitECandidate.Solver.Input.LocalSummarySequence

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

private theorem store_summary {F : Type} (source : PanSemStateExact 64 F) [DecidablePred source.shMemaddrs]
    (key : MlS) (bytes address : BitVec 64) (size : Nat) :
    let output := shMemStoreHOLExact source bytes address size
    (output.1 = none → output.2.locals key = source.locals key) ∧
    (∀ value,output.1 ≠ some (.returned value)) ∧ output.1 ≠ some .break ∧ output.1 ≠ some .continue := by
  classical
  dsimp only
  by_cases zero : size = 0
  · by_cases mapped : source.shMemaddrs address
    · cases reply : callFFIHOL source.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 size] (panWordToBytesHOL bytes false ++ panWordToBytesHOL address false) <;>
        simp_all [shMemStoreHOLExact]
    · simp [shMemStoreHOLExact,zero,mapped]
  · by_cases mapped : source.shMemaddrs (panByteAlignHOL address)
    · cases reply : callFFIHOL source.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 size] ((panWordToBytesHOL bytes false).take size ++ panWordToBytesHOL address false) <;>
        simp [shMemStoreHOLExact,zero,mapped,reply]
    · simp [shMemStoreHOLExact,zero,mapped]

/-- Shared stores can stop with an error or terminal FFI, but never change
caller locals or escape with a loop-control result. -/
theorem shared_store_local {F : Type} (key : MlS) (size : OpSize) (address value : ExpHOL 64) (source : PanSemStateFiniteExact 64 F) :
    LocalSummary key (.shMemStore size address value) source := by
  classical
  unfold LocalSummary
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · dsimp only [ofExact]
    exact store_summary source.toExact key _ _ _
  · simp


end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.shared_store_local
