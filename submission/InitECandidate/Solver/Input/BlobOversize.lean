import InitECandidate.Solver.Input.LengthGuard
import InitECandidate.Solver.Input.TrapStopped

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual encoded-length rejection stops before allocation/copy on all
outcomes. The input list itself is unrestricted; only its low64-bit length
is compared, exactly as in the original guest. -/
theorem oversize_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (installed : OriginalCode.Installed source.code)
    (oracle : source.ffi.oracle = InitE.sourceOracle) (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (shared : source.shMemaddrs = InitE.sharedDomain) (large : Guest.maxInputBytes < input.length % 2 ^ 64) :
    ∃ result target,evaluateHOLFiniteState source body = (some result,target) ∧
      (∀ value,result ≠ .returned value) ∧ target.clock ≤ source.clock ∧ source.clock - target.clock ≤ 1 := by
  let entered := lengthPost (WitnessRadix.QueryBranch.bind source "len" 0#64) input
  have len : entered.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 input.length))) := bind_lookup_same _ _ _
  have selected := oversized_read entered (BitVec.ofNat 64 input.length) len
  have active : 134217712 < (BitVec.ofNat 64 input.length).toNat := large
  simp only [if_pos active,WitnessRadix.QueryBranch.eval] at selected
  have currentInstalled : OriginalCode.Installed entered.code := installed
  obtain ⟨result,trapPost,trapRun,notReturned,upper,bounded⟩ := Trap.stopped entered 8#64 [.const 8#64] currentInstalled rfl
  have guardRun : evaluateHOLFiniteState entered guard = (some result,trapPost) := by
    rw [guard,evaluateHOLFiniteState_ite,selected]
    exact trapRun
  have afterLoad : evaluateHOLFiniteState entered (.seq guard afterGuard) = (some result,trapPost) :=
    WitnessRadix.StateSteps.stopped_sequence entered trapPost guard afterGuard result guardRun upper
  have actual : evaluateHOLFiniteState source body = (some result,restore source "len" trapPost) := by
    rw [length_entry source input oracle host shared,afterLoad]
  exact ⟨result,restore source "len" trapPost,actual,notReturned,upper,bounded⟩

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.oversize_execute
