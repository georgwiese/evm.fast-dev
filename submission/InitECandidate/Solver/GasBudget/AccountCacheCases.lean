import InitECandidate.Solver.GasBudget.AccountCachePrefix
import InitECandidate.Solver.Input.ReturnGuardException

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The observed cache branch either returns the actual retrieved word or
exposes the actual pre-state-provider call in the same reached state. -/
theorem cache_normal_cases (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (flag value : BitVec 64)
    (cell : source.locals.lookup (ofString "w") = some (Get.pair flag value))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source kind.afterGet = (some (.returned returned), post)) :
    (returned = .val (.word value) ∧ post = emptyLocalsHOLFinite source) ∨
      evaluateHOLFiniteState source kind.afterMiss = (some (.returned returned), post) := by
  rw [kind.cache_shape] at run
  rcases Input.return_guard_normal source post (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64))
      (.rfield 1 (localVar "w")) kind.afterMiss returned run with stopped | continued
  · obtain ⟨read, postEq⟩ := stopped
    have expected : eval source (.rfield 1 (localVar "w")) = some (.val (.word value)) := by
      simp [eval, evalHOLExact, toExact, localVar, cell, Get.pair]
    exact Or.inl ⟨Option.some.inj (read.symm.trans expected), postEq⟩
  · exact Or.inr continued

theorem cache_exception (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source kind.afterGet = (some (.exception identifier payload), post)) :
    evaluateHOLFiniteState source kind.afterMiss = (some (.exception identifier payload), post) := by
  rw [kind.cache_shape] at run
  exact Input.return_guard_exception source post _ _ kind.afterMiss identifier payload run

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.cache_normal_cases
#print axioms InitECandidate.Solver.GasBudget.AccountCache.cache_exception
