import InitECandidate.Solver.WitnessRadix.QueryBranchStep

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem restore_bind_other {F : Type} (saved state : PanSemStateFiniteExact 64 F)
    (name other : String) (word : BitVec 64) (different : ofString name ≠ ofString other) :
    restore saved name (bind state other word) = bind (restore saved name state) other word := by
  dsimp only [restore, bind, setVarHOLFinite]
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  cases old : saved.locals.lookup (ofString name) <;>
    by_cases atName : query = ofString name
  all_goals first
    | subst query
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        old, different, Ne.symm different]
    | simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        old, atName, Ne.symm atName]

theorem restore_bound {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (word : BitVec 64) : restore source name (bind source name word) = source := by
  dsimp only [restore, bind, setVarHOLFinite]
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  cases old : source.locals.lookup (ofString name) <;>
    by_cases atName : query = ofString name
  all_goals first
    | subst query
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL, old]
    | simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        old, atName, Ne.symm atName]

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.restore_bind_other
#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.restore_bound
