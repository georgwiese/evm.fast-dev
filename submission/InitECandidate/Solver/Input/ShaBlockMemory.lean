import InitECandidate.Solver.Input.ShaBlockSuffixMemory
import InitECandidate.Solver.Input.ShaGlobals

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original pair hashing passes accel+32 as the actual block, so the
optional copy is the real skipped branch before pack/FFI/unpack. -/
theorem block_in_place_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel)
    (block : source.locals.lookup (ofString "blk")=some (.val (.word (accel+32#64))))
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source blockBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  have read : eval source blockTest=some (.val (.word 0#64)) := by
    simp [eval,blockTest,localVar,evalHOLExact,evalListHOLExact,toExact,block,ready.accelerator,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guardRun : evaluateHOLFiniteState source blockGuard=(none,source) := by
    simp only [eval] at read
    rw [block_guard_shape,evaluateHOLFiniteState_ite,read]
    simp [evaluateHOLFiniteState_skip]
  rw [block_shape,StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)] at run
  exact block_suffix_memory source post pointer accel query ready stateAway accelAway value run

theorem block_environment_full (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer block : BitVec 64)
    (code : codeFn (ofString "sha256_block")=some (blockFormals,blockBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_block") (blockValues pointer block)=some (blockBody,callee,.one) ∧
      callee.lookup (ofString "stp")=some (.val (.word pointer)) ∧ callee.lookup (ofString "blk")=some (.val (.word block)) := by
  have valid : (blockFormals.map Prod.fst).Nodup ∧ blockFormals.length=(blockValues pointer block).length ∧
      ((blockFormals.zip (blockValues pointer block)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [blockFormals,blockValues,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_block") (blockValues pointer block)=some (blockBody,blockLocals pointer block,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [blockLocals,show ofString "stp"≠ofString "blk" from by decide],by rw [locals]; simp [blockLocals]⟩

/-- Real normal SHA block caller used by sha256_pair, with exact current
ABI and no oracle, hash-output, or future successful-call assumption. -/
theorem block_in_place_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (blockValues pointer (accel+32#64)))
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,stateLocal,blockLocal⟩ := block_environment_full source.code.lookup pointer (accel+32#64) (block_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "sha256_block") arguments (blockValues pointer (accel+32#64)) blockBody callee .one query args called
    (fun target value evaluated=>block_in_place_memory (callEntryStateHOLFinite source callee) target pointer accel query ⟨stateLocal,accelerator⟩ blockLocal stateAway accelAway value evaluated) run

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_in_place_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_environment_full
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_in_place_call_memory
