import InitECandidate.Solver.Input.VarList.FaultBody

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def resume (target : PanSemStateFiniteExact 64 Guest.HostMemory) :
    Option (PanSemResultExact 64)→Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory
  | none | some .continue=>evaluateHOLFiniteState target loop
  | some .break=>(none,target)
  | some result=>(some result,target)

/-- Exact real active-loop rule, retaining the evaluator's clock clamp and
all body outcomes. Signed index/count comparisons follow from natural bounds. -/
theorem active_unroll (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : Nat)
    (small : count<2^63) (active : index<count)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 count))))
    (positive : source.clock≠0) (result : Option (PanSemResultExact 64))
    (bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) loopBody=(result,target))
    (clock : target.clock≤source.clock-1) :
    evaluateHOLFiniteState source loop=resume target result := by
  classical
  have test:=loop_test_read source index count (by omega) small i n
  simp only [if_pos active] at test
  have finiteTest : evalHOLFinite source loopTest=some (.val (.word 1#64)) := test
  rw [loop_shape,evaluateHOLFiniteState_while_total,finiteTest]
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

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.active_unroll
