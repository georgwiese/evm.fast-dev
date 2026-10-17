import InitECandidate.Solver.WitnessRadix.ZeroEnvironment

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Entire actual aligned memzero call with restored caller locals and an
exact memory function/source-clock cost. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (values dst length))
    (code : source.code.lookup (ofString "memzero") = some (formals, body, .one))
    (small : length + 32 < 2 ^ 64) (multiple : length % 8 = 0) (aligned : dst.toNat % 8 = 0)
    (mapped : ∀ offset, offset + 8 ≤ length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (enough : price length + 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") arguments) =
      (none, { source with memory := finalMemory source.memory dst length, clock := source.clock - (price length + 1) }) := by
  classical
  obtain ⟨callee, lookup, dstLocal, lengthLocal⟩ := environment source.code.lookup dst length code
  let entry := callEntryStateHOLFinite source callee
  have run := execute_aligned entry dst length small multiple aligned dstLocal lengthLocal mapped
    (by change price length ≤ source.clock - 1; omega)
  have frame := final_frame entry dst length
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "memzero")
    arguments (values dst length) body callee .one (.val (.word 0#64)) (finalState entry dst length)
    args lookup (by omega) run (by simp [shapeEqHOL, shapeOfHOLExact])
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := source.locals }) frame
  have clockEq : source.clock - 1 - price length = source.clock - (price length + 1) := by omega
  simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, clockEq] using callRun.trans
    (congrArg (fun state : PanSemStateFiniteExact 64 F => (none, state)) restored)

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.call_execute
