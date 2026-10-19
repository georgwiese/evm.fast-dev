import InitECandidate.Solver.Mpt.StorageKeyProgram

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code)
    (enough : price address key scratch ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (some (.returned (.val (.word scratch))),emptyLocalsHOLFinite (resultState source address key scratch)) := by
  classical
  have argsFirst : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [buffer,localVar "addr",.const 20#64] = some (CopyGeneral.values scratch address 20) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,addressLocal,scratchGlobal,CopyGeneral.values]
  have firstMapped := AllocatedBytes.copy_mapped source address scratch 20 domain addressArena (scratchArena.weaken scratch 52 20 (by decide))
  have firstRun := CopyGeneral.call_execute source _ address scratch 20 argsFirst (CopyGeneral.original_code source.code installed)
    firstMapped (by decide) (by unfold price at enough; omega)
  let middle := CopyGeneral.callState source address scratch 20
  have argsSecond : evalListHOLFinite middle (h := fun query => Classical.propDecidable (middle.memaddrs query))
      [.op .add [buffer,.const 20#64],localVar "key",.const 32#64] = some (CopyGeneral.values (scratch + 20#64) key 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,middle,CopyGeneral.callState,keyLocal,scratchGlobal,
      valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values]
  have tailArena : AllocatedBytes.Arena (scratch + 20#64) 32 := scratchArena.subrange scratch 52 20 32 (by decide)
  have secondMapped := AllocatedBytes.copy_mapped middle key (scratch + 20#64) 32 domain keyArena tailArena
  have secondRun := CopyGeneral.call_execute middle _ key (scratch + 20#64) 32 argsSecond (CopyGeneral.original_code source.code installed)
    secondMapped (by decide) (by change _ ≤ source.clock - _; unfold price at enough; omega)
  change evaluateHOLFiniteState source firstCopy = _ at firstRun
  change evaluateHOLFiniteState middle secondCopy = _ at secondRun
  rw [body_shape,evaluateHOLFiniteState_seq_line780,firstRun]
  change evaluateHOLFiniteState middle (.seq secondCopy (.return buffer)) = _
  rw [evaluateHOLFiniteState_seq_line780,secondRun]
  simp [evaluateHOLFiniteState_return,evalHOLExact,buffer,toExact,CopyGeneral.callState,middle,scratchGlobal,resultState,
    shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.execute
