import InitECandidate.Solver.MutableTable.WitnessBuildProgram
import InitECandidate.Solver.WitnessRadix.CapacityBound

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocatedTail : ProgHOL 64:=.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail

/-- The original builder's real capacity declaration/doubling loop retains
its explicit power-of-two exponent and exposes the actual allocation tail. -/
theorem capacity_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count<2^31)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) (enough : 30≤source.clock) :
    ∃ target paid bits,evaluateHOLFiniteState source body=
      (let output:=evaluateHOLFiniteState target allocatedTail;(output.1,restore source "cap" output.2)) ∧
      paid≤30 ∧ 2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      target.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      ∀ name : MlS,ofString "cap"≠name→target.locals.lookup name=source.locals.lookup name := by
  let initial:=bind source "cap" 4#64
  have initialCount : initial.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))):=
    (bind_lookup_other _ "cap" "n" _ (by decide)).trans countLocal
  have initialCap : initial.locals.lookup (ofString "cap")=some (.val (.word 4#64)):=bind_lookup_same _ _ _
  obtain ⟨target,paid,bits,loopRun,budget,lower,upper,sufficient,capBound,capLocal,frame,others⟩:=Capacity.iterate initial count 2 30 small
    (by decide) (by decide) (by omega) (by omega) initialCount initialCap enough
  have clock : target.clock=source.clock-paid:=congrArg (fun state=>state.clock) frame
  have coreRun:=StateSteps.next_sequence initial target Constructor.capacityLoop allocatedTail loopRun (by change target.clock≤source.clock;omega)
  have setup : BuildEntry.Initializes source [("cap",.const 4#64)] initial (fun output=>restore source "cap" output):=
    .step 4#64 rfl (.done _)
  have scopeRun:=BuildEntry.declarations_execute setup (.seq Constructor.capacityLoop allocatedTail)
  rw [coreRun] at scopeRun
  refine ⟨target,paid,bits,?_,budget,lower,by omega,sufficient,capBound,capLocal,?_,?_⟩
  · rw [body_shape]
    exact scopeRun
  · exact frame
  · intro name different
    rw [others name different]
    simp [initial,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.capacity_entry
