import InitECandidate.Solver.CrepToLoopBound.Leaf
import InitECandidate.Solver.CrepToLoopBound.Tick
import InitECandidate.Solver.CrepToLoopBound.Seq
import InitECandidate.Solver.CrepToLoopBound.Dec
import InitECandidate.Solver.CrepToLoopBound.If
import InitECandidate.Solver.CrepToLoopBound.While
import InitECandidate.Solver.CrepToLoopBound.Call

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem lookupCodeFinite_eq_HOLFinite' {width : Nat} [NeZero width]
    (c : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width))
    (f : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeFiniteHOL c f args len = lookupCodeHOLFinite c.lookup f args len := by
  have h1 := lookupCodeFiniteHOL_lookup c f args len
  unfold lookupCodeHOLFinite
  split
  · rename_i hn
    rw [hn] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rfl
    | some val => rw [hF] at h1; simp at h1
  · rename_i body cl hs
    rw [hs] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rw [hF] at h1; simp at h1
    | some val =>
        obtain ⟨b, m⟩ := val
        rw [hF] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, hm⟩ := h1
        congr 2
        exact holFiniteMapExact_eq_of_lookup_eq hm

/-- All nineteen source constructors, with their literal guarded evaluator
induction hypotheses and the original semantic relations. -/
theorem compileCorrect {width : Nat} [NeZero width] {σ : Type} (limit : Nat) :
    ∀ (program : CrepProgHOL width) (source : CrepSemHOLState width σ),
      Simulation limit program source := by
  intro program source
  apply evalCrepSemHOLProgExact_induct (P := fun x => Simulation limit x.1 x.2)
  all_goals try simp only [crepExactEvalExpClassical_eq] at *
  · intro s
    exact simulateLeaf limit .skip s rfl
  · intro v e prog s ih safe bounded res s1 t ctxt l he hne hs hm hg hc hl
    exact simulateDec limit v e prog s safe bounded ih res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro lhss pop rhss s
    exact simulateLeaf limit (.primitive lhss pop rhss) s rfl
  · intro v src s
    exact simulateLeaf limit (.assign v src) s rfl
  · intro dst src s
    exact simulateLeaf limit (.store dst src) s rfl
  · intro dst src s
    exact simulateLeaf limit (.store32 dst src) s rfl
  · intro dst src s
    exact simulateLeaf limit (.storeByte dst src) s rfl
  · intro dst src s
    exact simulateLeaf limit (.storeGlob dst src) s rfl
  · intro op v ad s
    exact simulateLeaf limit (.shMem op v ad) s rfl
  · intro c1 c2 s ih2 ih1 safe bounded res s1 t ctxt l
    exact simulateSeq limit ctxt l c1 c2 s safe bounded ih2 ih1 t res s1
  · intro e c1 c2 s ih safe bounded res s1 t ctxt l he hne hs hm hg hc hl
    exact simulateIf limit e c1 c2 s safe bounded (fun w hw => ih _ w hw rfl) res s1 t ctxt l
      ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro n s
    exact simulateLeaf limit (.break n) s rfl
  · intro n s
    exact simulateLeaf limit (.continue n) s rfl
  · intro e c s ih1 ih2 ih3 safe bounded res s1 t ctxt l he hne hs hm hg hc hl
    exact simulateWhile limit e c s safe bounded
      (fun w r s1' ⟨h1, h2, h3, h4, h5⟩ => ih1 _ w r s1' _ 0 h1 rfl h2 h3 h4.symm h5 rfl rfl)
      (fun w r s1' ⟨h1, h2, h3, h4, h5⟩ => ih2 _ w r s1' h1 rfl h2 h3 h4.symm h5)
      (fun w ⟨h1, h2, h3⟩ => ih3 _ w h1 rfl h2 h3)
      res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro es s
    exact simulateLeaf limit (.return es) s rfl
  · intro eid s
    exact simulateLeaf limit (.raise eid) s rfl
  · intro s
    exact simulateTick limit s
  · intro caltyp fname argexps s ihh ihb safe bounded res s1 t ctxt l he hne hs hm hg hc hl
    have hfun : crepExactEvalExpClassical s = evalCrepSemHOLExp s :=
      funext (crepExactEvalExpClassical_eq s)
    exact simulateCall limit caltyp fname argexps s safe bounded
      (fun args prog newlocals st eid rts p ⟨h1, h2, h3, h4, h5, h6⟩ =>
        ihh args (prog, newlocals) prog newlocals _ _ st _ eid _ _ _ _ eid p
          (by rw [hfun]; exact h1) (by rw [← lookupCodeFinite_eq_HOLFinite']; exact h2) rfl
          (by subst h6; simpa using h3) h4 h5.symm rfl rfl rfl h6 rfl rfl rfl rfl)
      (fun args prog newlocals ⟨h1, h2, h3, h4⟩ =>
        ihb args (prog, newlocals) prog newlocals (by rw [hfun]; exact h1)
          (by rw [← lookupCodeFinite_eq_HOLFinite']; exact h2) rfl
          (by cases caltyp with
              | none => simp
              | some x => obtain ⟨rts, y⟩ := x; simpa using h3) h4)
      res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  · intro f p1 l1 p2 l2 s
    exact simulateLeaf limit (.extCall f p1 l1 p2 l2) s rfl

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.compileCorrect
