import InitECandidate.Solver.CrepToLoopBound.SimplifyCost
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.Basis.Pure.MlString

def entriesSafe {width : Nat} [NeZero width] (limit : Nat)
    (entries : List (MlString × List Nat × CrepProgHOL width)) : Bool :=
  entries.all fun entry => decide (ceiling entry.2.2 ≤ limit)

theorem entriesSafe_codeSafe {width : Nat} [NeZero width] (limit : Nat)
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (safe : entriesSafe limit entries = true) : CodeSafe limit (alistToFmapCodeExact entries) := by
  intro name parameters program found
  rw [alistToFmapCodeExact, HolFiniteMapExact.lookup_updateList] at found
  have member := flookup_fupdateList_reverse_mem' entries name (parameters, program) found
  have checked := List.all_eq_true.mp safe (name, parameters, program) member
  exact of_decide_eq_true checked

theorem codeSafe_simplify {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (source : CrepSemHOLState width F) (safe : CodeSafe limit source.code) :
    CodeSafe limit (crepSimpMapcsHOL source).code := by
  intro name parameters program found
  simp only [crepSimpMapcsHOL, HolFiniteMapExact.lookup_map2] at found
  cases original : source.code.lookup name with
  | none => simp [original] at found
  | some descriptor =>
    rcases descriptor with ⟨originalParameters, originalBody⟩
    simp only [original, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    rcases found with ⟨rfl, rfl⟩
    exact Nat.le_trans (simplifyCeiling originalBody) (safe name originalParameters originalBody original)

theorem entriesSafe_simplifiedCode {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (entries : List (MlString × List Nat × CrepProgHOL width))
    (source : CrepSemHOLState width F) (code : source.code = alistToFmapCodeExact entries)
    (safe : entriesSafe limit entries = true) : CodeSafe limit (crepSimpMapcsHOL source).code := by
  apply codeSafe_simplify limit source
  rw [code]
  exact entriesSafe_codeSafe limit entries safe

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.entriesSafe_codeSafe
#print axioms InitECandidate.Solver.CrepToLoopBound.codeSafe_simplify
#print axioms InitECandidate.Solver.CrepToLoopBound.entriesSafe_simplifiedCode
