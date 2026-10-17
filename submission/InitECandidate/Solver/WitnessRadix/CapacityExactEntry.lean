import InitECandidate.Solver.WitnessRadix.CapacityExact
import InitECandidate.Solver.WitnessRadix.BuildEntry
import InitECandidate.Solver.WitnessRadix.CapacityBound

namespace InitECandidate.Solver.WitnessRadix.Capacity
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original builder's real capacity declaration/doubling loop retains
its explicit power-of-two exponent and exposes the actual allocation tail. -/
theorem declare_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (count : Nat) (small : count<2^31)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) (enough : 30≤source.clock)
    (continuation : ProgHOL 64) :
    ∃ target paid bits,evaluateHOLFiniteState source (.dec (ofString "cap") .one (.const 4#64) (.seq Constructor.capacityLoop continuation))=
      (let output:=evaluateHOLFiniteState target continuation;(output.1,restore source "cap" output.2)) ∧
      paid≤30 ∧ 2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      target.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      (∀ name : MlS,ofString "cap"≠name→target.locals.lookup name=source.locals.lookup name) ∧
      bits=2+paid ∧ (2^bits<4*count+4 ∨ bits=2) := by
  let initial:=bind source "cap" 4#64
  have initialCount : initial.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))):=
    (bind_lookup_other _ "cap" "n" _ (by decide)).trans countLocal
  have initialCap : initial.locals.lookup (ofString "cap")=some (.val (.word 4#64)):=bind_lookup_same _ _ _
  obtain ⟨target,paid,bits,loopRun,budget,lower,upper,sufficient,capBound,capLocal,frame,others,expPaid,minimal⟩:=iterate_exact initial count 2 30 small
    (by decide) (by decide) (by omega) (by omega) initialCount initialCap enough
  have clock : target.clock=source.clock-paid:=congrArg (fun state=>state.clock) frame
  have coreRun:=StateSteps.next_sequence initial target Constructor.capacityLoop continuation loopRun (by change target.clock≤source.clock;omega)
  have setup : BuildEntry.Initializes source [("cap",.const 4#64)] initial (fun output=>restore source "cap" output):=
    .step 4#64 rfl (.done _)
  have scopeRun:=BuildEntry.declarations_execute setup (.seq Constructor.capacityLoop continuation)
  rw [coreRun] at scopeRun
  refine ⟨target,paid,bits,?_,budget,lower,by omega,sufficient,capBound,capLocal,?_,?_,expPaid,minimal⟩
  · exact scopeRun
  · exact frame
  · intro name different
    rw [others name different]
    simp [initial,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

end InitECandidate.Solver.WitnessRadix.Capacity

#print axioms InitECandidate.Solver.WitnessRadix.Capacity.declare_execute
