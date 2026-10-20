import InitECandidate.Solver.Input.BlobOversize
import InitECandidate.Solver.Input.BlobCallEnvironment

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An oversized original input call cannot enter its lexical continuation.
Both caller and trap ticks are included on every outcome, with no funding
premise and no assumed terminal FFI reply. -/
theorem oversize_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (name : MlS) (shape : ShapeHOL) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (oracle : source.ffi.oracle = InitE.sourceOracle) (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (shared : source.shMemaddrs = InitE.sharedDomain) (large : Guest.maxInputBytes < input.length % 2 ^ 64) :
    ∃ result target,evaluateHOLFiniteState source (.decCall name shape (ofString "input_blob") [] continuation) = (some result,target) ∧
      (∀ value,result ≠ .returned value) ∧ target.clock ≤ source.clock ∧ source.clock - target.clock ≤ 2 := by
  obtain ⟨callee,called⟩ := environment source.code.lookup (original_code source.code installed)
  by_cases zero : source.clock = 0
  · refine ⟨.timeOut,emptyLocalsHOLFinite source,?_,?_,Nat.le_refl _,?_⟩
    · rw [evaluateHOLFiniteState_decCall_total]
      simp [evalListHOLFinite,evalListHOLExact,called,zero]
    · intro value
      simp
    · simp [zero]
  · let entry := callEntryStateHOLFinite source callee
    obtain ⟨result,post,run,notReturned,upper,cost⟩ := oversize_execute entry input installed oracle host shared large
    have fixed := WitnessRadix.StateSteps.fixed_clock entry post (some result) upper
    dsimp only [entry] at run fixed
    have actual := evaluateHOLFiniteState_decCall_total source name shape (ofString "input_blob") [] continuation
    simp only [show evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [] = some [] from rfl,
      called,if_neg zero,run,fixed] at actual
    rw [actual]
    cases result with
    | returned value => exact False.elim (notReturned value rfl)
    | _ =>
      refine ⟨_,_,rfl,?_,?_,?_⟩
      · intro value
        simp
      · change post.clock ≤ source.clock
        change post.clock ≤ source.clock - 1 at upper
        omega
      · change source.clock - post.clock ≤ 2
        change source.clock - 1 - post.clock ≤ 1 at cost
        omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.oversize_call
