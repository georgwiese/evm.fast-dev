import InitECandidate.Solver.Input.MainBlsFpProgram

namespace InitECandidate.Solver.Input.Main.BlsFpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

private theorem offset_aligned (pointer : BitVec 64) (extent offset : Nat) (arena : AllocatedBytes.Arena pointer extent)
    (aligned : pointer.toNat % 8 = 0) (multiple : offset % 8 = 0) (inside : offset ≤ extent) :
    (byteAddress pointer offset).toNat % 8 = 0 := by
  rw [byteAddress_toNat pointer offset (by have := arena.upper; omega)]
  omega

/-- Both original memory helpers run with their actual mapped arenas. The
copy reads the current constant-table bytes and retains its exact real memory. -/
theorem memory_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer constants : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (params : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word pointer)))
    (zero : source.globals.lookup (ofString "fp_accel_zero") = some (.val (.word (pointer + 96#64))))
    (constantBinding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (paramsArena : AllocatedBytes.Arena pointer 240) (paramsAligned : pointer.toNat % 8 = 0)
    (constantArena : AllocatedBytes.Arena constants 7136) (constantAligned : constants.toNat % 8 = 0) (enough : 8 ≤ source.clock) :
    evaluateHOLFiniteState source memoryTail =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {memoryTemplate source pointer constants with clock := source.clock - 8}) := by
  have zeroArena : AllocatedBytes.Arena (pointer + 96#64) 48 := paramsArena.subrange pointer 240 96 48 (by decide)
  have zeroAligned : (pointer + 96#64).toNat % 8 = 0 := offset_aligned pointer 240 96 paramsArena paramsAligned (by decide) (by decide)
  have zeroArgs : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [.var .global (ofString "fp_accel_zero"),.const 48#64] = some (Zero.values (pointer + 96#64) 48) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zero,Zero.values]
  have zeroRun := Zero.call_execute source _ (pointer + 96#64) 48 zeroArgs (Zero.original_code source.code installed) (by decide) (by decide) zeroAligned
    (by intro offset inside aligned; exact AllocatedBytes.word_mapped source (pointer + 96#64) 48 offset domain zeroArena (by omega) zeroAligned aligned)
    (by change 4 ≤ source.clock; omega)
  let zeroed := {source with memory := Zero.finalMemory source.memory (pointer + 96#64) 48,clock := source.clock - 4}
  have inputArena : AllocatedBytes.Arena (constants + 48#64) 48 := constantArena.subrange constants 7136 48 48 (by decide)
  have outputArena : AllocatedBytes.Arena (pointer + 144#64) 48 := paramsArena.subrange pointer 240 144 48 (by decide)
  have inputAligned : (constants + 48#64).toNat % 8 = 0 := offset_aligned constants 7136 48 constantArena constantAligned (by decide) (by decide)
  have outputAligned : (pointer + 144#64).toNat % 8 = 0 := offset_aligned pointer 240 144 paramsArena paramsAligned (by decide) (by decide)
  have mask : CopyGeneral.aligned (constants + 48#64) (pointer + 144#64) := Copy32.alignment_mask _ _ inputAligned outputAligned
  have copyPrice : CopyGeneral.cost (constants + 48#64) (pointer + 144#64) 48 = 3 := by
    simp [CopyGeneral.cost,mask,CopyWords.prefixCost,CopyWords.prefixIndex,CopyBytes.suffixCost]
  have copyArgs : evalListHOLFinite zeroed (h := fun query => Classical.propDecidable (zeroed.memaddrs query))
      [.op .add [.var .global (ofString "fp_accel_params"),.const 144#64],.op .add [.var .global (ofString "bls_c"),.const 48#64],.const 48#64] =
      some (CopyGeneral.values (pointer + 144#64) (constants + 48#64) 48) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroed,params,constantBinding,CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have copied := CopyGeneral.call_execute zeroed _ (constants + 48#64) (pointer + 144#64) 48 copyArgs
    (CopyGeneral.original_code source.code installed) (AllocatedBytes.copy_mapped zeroed _ _ 48 domain inputArena outputArena) (by decide)
    (by rw [copyPrice]; change 3 + 1 ≤ source.clock - 4; omega)
  have copyRun : evaluateHOLFiniteState zeroed copyCall = (none,{memoryTemplate source pointer constants with clock := source.clock - 8}) := by
    simpa only [copyCall,CopyGeneral.callState,copyPrice,zeroed,memoryTemplate,Nat.sub_sub,show 4 + (3 + 1) = 8 from rfl] using copied
  rw [memoryTail,StateSteps.next_sequence source zeroed zeroCall _ zeroRun (by change source.clock - 4 ≤ source.clock; omega),
    StateSteps.next_sequence zeroed {memoryTemplate source pointer constants with clock := source.clock - 8} copyCall _ copyRun (by change source.clock - 8 ≤ source.clock - 4; omega)]
  exact BuildEntry.zero_return {memoryTemplate source pointer constants with clock := source.clock - 8}

end InitECandidate.Solver.Input.Main.BlsFpInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.memory_execute
