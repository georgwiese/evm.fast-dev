import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem restore_lookup_other {F : Type} (saved state : PanSemStateFiniteExact 64 F) (name key : String)
    (other : ofString key ≠ ofString name) :
    (restore saved name state).locals.lookup (ofString key) = state.locals.lookup (ofString key) := by
  change (HolFiniteMapExact.resVarEq state.locals (ofString name, saved.locals.lookup (ofString name))).lookup (ofString key) = _
  rw [lookup_resVarEq_toExact]
  cases saved.locals.lookup (ofString name) <;> simp [resVarHOLExact, FUPDATE, FDOMSUB, other]

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.restore_lookup_other
