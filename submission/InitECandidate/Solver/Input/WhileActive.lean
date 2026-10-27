import Guest.Model
import InitECandidate.Solver.WitnessRadix.StateSteps
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

noncomputable def whileResume (target : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64) (body : ProgHOL 64) :
    Option (PanSemResultExact 64)→Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory
  | none | some .continue=>evaluateHOLFiniteState target (.while condition body)
  | some .break=>(none,target)
  | some result=>(some result,target)

theorem while_active (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64) (body : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (test : eval source condition=some (.val (.word 1#64))) (positive : source.clock≠0)
    (bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) body=(result,target)) (clock : target.clock≤source.clock-1) :
    evaluateHOLFiniteState source (.while condition body)=whileResume target condition body result := by
  classical
  have bridge : evalHOLFinite source condition=eval source condition :=
    congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h condition) (Subsingleton.elim _ _)
  have finiteTest:=bridge.trans test
  rw [evaluateHOLFiniteState_while_total,finiteTest]
  simp only []
  simp only [if_neg positive]
  rw [bodyRun,WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result clock]
  split
  · cases result with
    | none=>rfl
    | some result=>cases result <;>rfl
  · rename_i impossible
    exact (impossible (by decide)).elim

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.while_active
