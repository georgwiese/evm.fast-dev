import InitECandidate.Solver.Input.OffsetsWalk
import InitECandidate.Solver.Input.OffsetsFaultStep

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def resume {F : Type} (target : PanSemStateFiniteExact 64 F) : Option (PanSemResultExact 64)→Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 F
  | none | some .continue=>evaluateHOLFiniteState target loop
  | some .break=>(none,target)
  | some result=>(some result,target)

/-- Exact active-iteration rule for the literal validator loop, retaining the
real evaluator's clock clamp and all abnormal body results. -/
theorem active_unroll {F : Type} (source target : PanSemStateFiniteExact 64 F) (index count : Nat)
    (small : count≤8) (active : index<count)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (positive : source.clock≠0) (result : Option (PanSemResultExact 64))
    (bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) loopBody=(result,target))
    (clock : target.clock≤source.clock-1) :
    evaluateHOLFiniteState source loop=resume target result := by
  classical
  have test:=condition_read source index count (by omega) small indexLocal countLocal
  simp only [if_pos active] at test
  rw [loop_shape,evaluateHOLFiniteState_while_total,test]
  simp only []
  simp only [if_neg positive]
  rw [bodyRun,WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result clock]
  split
  · simp only []
    rw [←loop_shape]
    cases result with
    | none=>rfl
    | some result=>cases result <;>rfl
  · rename_i impossible
    exact (impossible (by decide)).elim

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.active_unroll
