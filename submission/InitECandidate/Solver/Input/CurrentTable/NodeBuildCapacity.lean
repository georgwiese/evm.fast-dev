import InitECandidate.Solver.Input.CurrentTable.NodeBuildSyntax
import InitECandidate.Solver.WitnessRadix.CapacityBound
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same actual capacity execution selects the real current table
allocation caller. No table allocation or insertion success is supplied. -/
theorem capacity_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count<2^31)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) (enough : 30≤source.clock) :
    ∃ target paid bits,evaluateHOLFiniteState source body=
      (let output:=evaluateHOLFiniteState target allocatedTail;(output.1,restore source "cap" output.2)) ∧
      paid≤30 ∧ 2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      target.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      target.clock=source.clock-paid ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      ∀ name : MlS,ofString "cap"≠name→target.locals.lookup name=source.locals.lookup name := by
  let initial:=bind source "cap" 4#64
  have initialCount : initial.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) :=
    (bind_lookup_other _ "cap" "n" _ (by decide)).trans countLocal
  have initialCap : initial.locals.lookup (ofString "cap")=some (.val (.word 4#64)) := bind_lookup_same _ _ _
  obtain ⟨target,paid,bits,loopRun,budget,lower,upper,sufficient,capBound,capLocal,frame,others⟩:=Capacity.iterate initial count 2 30 small
    (by decide) (by decide) (by omega) (by omega) initialCount initialCap enough
  have clock : target.clock=source.clock-paid := congrArg PanSemStateFiniteExact.clock frame
  have coreRun:=StateSteps.next_sequence initial target Constructor.capacityLoop allocatedTail loopRun (by change target.clock≤source.clock; omega)
  have scopeRun:=ScalarScope.declare_execute source _ "cap" (.const 4#64) 4#64 (.seq Constructor.capacityLoop allocatedTail) _ rfl coreRun
  refine ⟨target,paid,bits,?_,budget,lower,by omega,sufficient,capBound,capLocal,clock,?_,?_⟩
  · rw [body_shape]
    exact scopeRun
  · have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) frame
    exact projected
  · intro name different
    rw [others name different]
    simp [initial,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

/-- Every real builder outcome either stops within the capacity allowance
or reaches the actual current table allocation, retaining its chosen power
and complete nonlocal frame. -/
theorem capacity_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count<2^31)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤30 ∨ ∃ target inner paid bits,
      paid≤30 ∧ 2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      target.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      target.clock=source.clock-paid ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      (∀ name : MlS,ofString "cap"≠name→target.locals.lookup name=source.locals.lookup name) ∧
      evaluateHOLFiniteState target allocatedTail=(outcome,inner) ∧ post=restore source "cap" inner := by
  by_cases enough : 30≤source.clock
  · obtain ⟨target,paid,bits,actual,budget,lower,upper,sufficient,capBound,capLocal,clock,frame,others⟩:=capacity_entry source count small countLocal enough
    rw [actual] at run
    have observed:=congrArg Prod.fst run
    have endpoint:=congrArg Prod.snd run
    exact Or.inr ⟨target,(evaluateHOLFiniteState target allocatedTail).2,paid,bits,budget,lower,upper,sufficient,capBound,capLocal,clock,frame,others,
      Prod.ext observed rfl,endpoint.symm⟩
  · exact Or.inl (by omega)

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.capacity_entry
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.capacity_trace
