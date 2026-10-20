import InitECandidate.Solver.Input.ShaCallCost

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- sha256_pair uses the real accelerator input buffer directly. Its block
call skips the optional copy, regardless of contents or later FFI outcome. -/
theorem block_in_place_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accel : BitVec 64)
    (blockLocal : source.locals.lookup (ofString "blk")=some (.val (.word (accel+32#64))))
    (workspace : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel))) :
    source.clock-(evaluateHOLFiniteState source blockBody).2.clock≤8 := by
  have read : eval source blockTest=some (.val (.word 0#64)) := by
    simp [eval,blockTest,localVar,evalHOLExact,evalListHOLExact,toExact,blockLocal,workspace,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guardRun : evaluateHOLFiniteState source blockGuard=(none,source) := by
    simp only [eval] at read
    rw [block_guard_shape,evaluateHOLFiniteState_ite,read]
    simp [evaluateHOLFiniteState_skip]
  rw [block_shape,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
  exact block_suffix_price source.code source rfl

theorem block_in_place_call_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (blockValues stp (accel+32#64)))
    (workspace : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel))) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "sha256_block") arguments)).2.clock≤9 := by
  obtain ⟨callee,called,blockLocal⟩ := block_environment source.code.lookup stp (accel+32#64) (block_code source.code installed)
  have cost := block_in_place_price (callEntryStateHOLFinite source callee) accel blockLocal workspace
  exact ClockCost.call_current source destination (ofString "sha256_block") arguments (blockValues stp (accel+32#64)) blockBody callee .one 8 args called cost

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_in_place_price
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_in_place_call_price
