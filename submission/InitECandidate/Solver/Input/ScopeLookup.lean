import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem restore_other {F : Type} (saved source : PanSemStateFiniteExact 64 F) (scope name : String)
    (different : ofString scope≠ofString name) :
    (restore saved scope source).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  simp only [restore,HolFiniteMapExact.holFmapAsFiniteSupportResultWitness_resVarEq]
  cases old : saved.locals.lookup (ofString scope) <;>
    simp [old,FDOMSUB_HOL,FUPDATE_HOL,different,Ne.symm different]

end InitECandidate.Solver.Input.ScalarScope

#print axioms InitECandidate.Solver.Input.ScalarScope.restore_other
