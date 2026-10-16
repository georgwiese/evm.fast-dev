import InitECandidate.Solver.CrepToLoopBound.ExpressionCost
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack

theorem expressionSimulation {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s e = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        ck ≤ expCost e ∧
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s e v t ctxt tmp l p le ntmp nl premises
  obtain ⟨extra, post, targetRun, value, related, memory, globals, code, locals⟩ :=
    Flapjack.crepToLoop_comp_exp_preserves_eval s e v t ctxt tmp l p le ntmp nl premises
  have generated := expressionCost ctxt tmp l e
  rw [premises.2.2.2.2.2.2.1] at generated
  have compiledShape := nestedSeqCost p (expCost e) generated
  have budget := straightClock (loopNestedSeqHOL p) {t with clock := t.clock + extra} compiledShape.1
  rw [targetRun, compiledShape.2] at budget
  have initialClock : s.clock = t.clock := premises.2.1.2.2.1
  have finalClock : s.clock = post.clock := related.2.2.1
  refine ⟨extra, post, ?_, targetRun, value, related, memory, globals, code, locals⟩
  dsimp only at budget
  omega

theorem expressionsSimulation {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ)
      (vs : List (HolWordLab width)) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet),
      es.mapM (evalCrepSemHOLExp s) = some vs ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpsHOLExact ctxt tmp l es = (p, les, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        ck ≤ expsCost es ∧
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        les.mapM (LoopSemStateFiniteExact.eval st) = some (vs.map wlabWlocExact) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro es s vs t ctxt tmp l p les ntmp nl premises
  obtain ⟨extra, post, targetRun, value, related, memory, globals, code, locals⟩ :=
    Flapjack.crepToLoop_comp_exps_preserves_eval es s vs t ctxt tmp l p les ntmp nl premises
  have generated := expressionsCost ctxt tmp l es
  rw [premises.2.2.2.2.2.2.1] at generated
  have compiledShape := nestedSeqCost p (expsCost es) generated
  have budget := straightClock (loopNestedSeqHOL p) {t with clock := t.clock + extra} compiledShape.1
  rw [targetRun, compiledShape.2] at budget
  have initialClock : s.clock = t.clock := premises.2.1.2.2.1
  have finalClock : s.clock = post.clock := related.2.2.1
  refine ⟨extra, post, ?_, targetRun, value, related, memory, globals, code, locals⟩
  dsimp only at budget
  omega

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.expressionSimulation
#print axioms InitECandidate.Solver.CrepToLoopBound.expressionsSimulation
