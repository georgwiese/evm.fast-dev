import InitECandidate.Solver.GasBudget.AccountOptionalCachePrefix
import InitECandidate.Solver.GasBudget.AccountCacheCases
import InitECandidate.Solver.Input.ReturnGuardException

namespace InitECandidate.Solver.GasBudget.AccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The observed cache branch either returns the actual retrieved word or
exposes the actual pre-state-provider call in the same reached state. -/
theorem cache_normal_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (flag value : BitVec 64)
    (cell : source.locals.lookup (ofString "w") = some (Get.pair flag value))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source afterGet = (some (.returned returned), post)) :
    (returned = .val (.word value) ∧ post = emptyLocalsHOLFinite source) ∨
      evaluateHOLFiniteState source afterMiss = (some (.returned returned), post) := by
  exact AccountCache.cache_normal_cases .transaction source post flag value cell returned run

theorem cache_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source afterGet = (some (.exception identifier payload), post)) :
    evaluateHOLFiniteState source afterMiss = (some (.exception identifier payload), post) := by
  exact AccountCache.cache_exception .transaction source post identifier payload run

end InitECandidate.Solver.GasBudget.AccountOptional

#print axioms InitECandidate.Solver.GasBudget.AccountOptional.cache_normal_cases
#print axioms InitECandidate.Solver.GasBudget.AccountOptional.cache_exception
