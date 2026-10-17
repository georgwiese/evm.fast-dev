import InitECandidate.Solver.Input.UDivMod.Frame

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem finite_eval (source : PanSemStateFiniteExact 64 Guest.HostMemory) [DecidablePred source.memaddrs] (expression : ExpHOL 64) :
    evalHOLFinite source expression=eval source expression := by
  exact congrArg (fun h : DecidablePred source.memaddrs => @evalHOLExact 64 Guest.HostMemory _ source.toExact h expression) (Subsingleton.elim _ _)

/-- The actual division loop always finishes within its remaining at-most64
rounds. This statement accounts for execution and frames; it does not assume
or assert arithmetic division correctness. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat)
    (small : index≤64) (enough : index≤source.clock)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (qLocal : source.locals.lookup (ofString "q")=some (.val (.word q)))
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word r)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    ∃ target finalQ finalR,
      evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-index} ∧
      target.locals.lookup (ofString "i")=some (.val (.word 0#64)) ∧
      target.locals.lookup (ofString "q")=some (.val (.word finalQ)) ∧
      target.locals.lookup (ofString "r")=some (.val (.word finalR)) ∧
      (∀ name : MlS,name≠ofString "i"→name≠ofString "q"→name≠ofString "r"→target.locals.lookup name=source.locals.lookup name) := by
  classical
  induction index generalizing source q r with
  | zero=>
    have test : evalHOLFinite source loopTest=some (.val (.word 0#64)) := by
      rw [finite_eval]
      simpa only [eval,Nat.lt_irrefl,↓reduceIte] using loop_test source 0 (by decide) iLocal
    refine ⟨source,q,r,?_,by simp, iLocal,qLocal,rLocal,by intros; rfl⟩
    rw [loop,evaluateHOLFiniteState_while_total,test]
    simp
  | succ index ih=>
    let entry:=decClockHOLFinite source
    let next:=step entry a b q r (index+1)
    have nextState : next={entry with locals:=next.locals}:=step_state entry a b q r (index+1)
    have nextClock : next.clock=source.clock-1:=congrArg PanSemStateFiniteExact.clock nextState
    have bodyRun:=body_execute entry a b q r (index+1) (by omega) small aLocal bLocal qLocal rLocal iLocal
    have fields:=step_fields entry a b q r (index+1) qLocal
    have nextA : next.locals.lookup (ofString "a")=some (.val (.word a)) :=
      (step_other entry a b q r (index+1) (ofString "a") (by decide) (by decide) (by decide)).trans aLocal
    have nextB : next.locals.lookup (ofString "b")=some (.val (.word b)) :=
      (step_other entry a b q r (index+1) (ofString "b") (by decide) (by decide) (by decide)).trans bLocal
    obtain ⟨target,finalQ,finalR,tailRun,targetState,finalI,finalQRead,finalRRead,others⟩:=
      ih next (nextQ a b q r (index+1)) (nextR a b r (index+1)) (by omega) (by omega) nextA nextB fields.2.1 fields.2.2 (by simpa using fields.1)
    have targetClock : target.clock=next.clock-index:=congrArg PanSemStateFiniteExact.clock targetState
    have targetClockBound : target.clock≤source.clock-1 := by omega
    have test : evalHOLFinite source loopTest=some (.val (.word 1#64)) := by
      rw [finite_eval]
      simpa only [eval,show 0<index+1 from by omega,↓reduceIte] using loop_test source (index+1) small iLocal
    refine ⟨target,finalQ,finalR,?_,?_,finalI,finalQRead,finalRRead,?_⟩
    · rw [loop,evaluateHOLFiniteState_while_total,test]
      simp only []
      simp only [if_neg (show source.clock≠0 by omega)]
      rw [bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (by change next.clock≤source.clock-1; omega)]
      simp only []
      split
      · exact tailRun
      · rename_i impossible
        exact (impossible (by decide)).elim
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,clock:=source.clock-1-index} at targetState
      have subtract : source.clock-1-index=source.clock-(index+1) := by omega
      simpa only [subtract] using targetState
    · intro name notI notQ notR
      exact (others name notI notQ notR).trans (step_other entry a b q r (index+1) name notI notQ notR)

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.loop_execute
