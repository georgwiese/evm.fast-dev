import InitECandidate.Solver.GasBudget.AccountCacheProgram

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString MutableTable WitnessRadix.QueryBranch

/-- The actual typed cache test either enters the real miss continuation
at the same state or returns its retrieved word without a helper tick. -/
theorem cache_dispatch (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag value : BitVec 64)
    (cell : source.locals.lookup (ofString "w")=some (Get.pair flag value)) :
    evaluateHOLFiniteState source kind.afterGet=if flag=0#64 then evaluateHOLFiniteState source kind.afterMiss
      else (some (.returned (.val (.word value))),emptyLocalsHOLFinite source) := by
  rw [kind.cache_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  by_cases zero : flag=0#64
  all_goals simp [evalHOLExact,localVar,toExact,cell,Get.pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,
    evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,shapeOfHOLExact,sizeOfShapeWithContextHOL,emptyLocalsHOLFinite]

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.cache_dispatch
