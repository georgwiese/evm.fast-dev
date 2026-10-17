import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem state_of_locals_frame {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (locals : source.locals = target.locals)
    (fields : emptyLocalsHOLFinite source = emptyLocalsHOLFinite target) : source = target := by
  cases source
  cases target
  cases locals
  cases fields
  rfl

theorem restore_saved {F : Type} (first second state : PanSemStateFiniteExact 64 F) (name : String)
    (saved : first.locals.lookup (ofString name) = second.locals.lookup (ofString name)) :
    restore first name state = restore second name state := by
  simp only [restore, saved]

/-- Restoring two scoped temporaries recovers exactly the original locals
when every other binding was preserved. Nonlocal fields stay at target. -/
theorem restore_two {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name other : String) (different : ofString name ≠ ofString other)
    (outside : ∀ query : MlS, query ≠ ofString name → query ≠ ofString other →
      target.locals.lookup query = source.locals.lookup query) :
    restore source name (restore source other target) = { target with locals := source.locals } := by
  dsimp only [restore]
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  cases oldName : source.locals.lookup (ofString name) <;>
    cases oldOther : source.locals.lookup (ofString other) <;>
    by_cases atName : query = ofString name
  all_goals first
    | subst query
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL, oldName]
    | skip
  all_goals by_cases atOther : query = ofString other
  all_goals first
    | subst query
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        oldName, oldOther, different, Ne.symm different]
    | simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        oldName, oldOther, atName, atOther, Ne.symm atName, Ne.symm atOther] using outside query atName atOther

theorem restore_two_frame {F : Type} (source target desired : PanSemStateFiniteExact 64 F)
    (name other : String) (different : ofString name ≠ ofString other)
    (outside : ∀ query : MlS, query ≠ ofString name → query ≠ ofString other →
      target.locals.lookup query = source.locals.lookup query)
    (locals : desired.locals = source.locals)
    (fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite desired) :
    restore source name (restore source other target) = desired := by
  rw [restore_two source target name other different outside]
  apply state_of_locals_frame
  · exact locals.symm
  · simpa only [emptyLocalsHOLFinite] using fields

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.restore_two_frame
