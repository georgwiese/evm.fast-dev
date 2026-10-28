import InitECandidate.Solver.Input.CurrentTable.NodeBuildCapacity
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A real normal capacity exit supplies its chosen power even if the
incoming clock was below the coarse30-tick allowance. Clock padding is
justified by that same observed non-timeout run, never future funding. -/
theorem capacity_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (small : count<2^31)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word 4#64)))
    (normal : evaluateHOLFiniteState source Constructor.capacityLoop=(none,post)) :
    ∃ bits,2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      post.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      LocalEffects.erase post=LocalEffects.erase source ∧ source.clock-post.clock≤30 ∧
      ∀ name : MlS,ofString "cap"≠name → post.locals.lookup name=source.locals.lookup name := by
  let padded := {source with clock:=source.clock+30}
  obtain ⟨target,paid,bits,run,budget,lower,upper,sufficient,capBound,cap,frame,others⟩ :=
    Capacity.iterate padded count 2 30 small (by decide) (by decide) (by omega) (by omega) countCell capCell (by simp [padded])
  have shifted := panPropsEvaluateAddClockEq Constructor.capacityLoop source none post 30 ⟨normal,by decide⟩
  have targetEq : target={post with clock:=post.clock+30} := congrArg Prod.snd (run.symm.trans shifted)
  have postCap : post.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) := by
    rw [targetEq] at cap
    exact cap
  have physical := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) frame
  have erased : LocalEffects.erase post=LocalEffects.erase source := by
    rw [targetEq] at physical
    exact physical
  have clock := congrArg PanSemStateFiniteExact.clock frame
  rw [targetEq] at clock
  change post.clock+30=source.clock+30-paid at clock
  refine ⟨bits,lower,by omega,sufficient,capBound,postCap,erased,by omega,?_⟩
  intro name different
  have kept := others name different
  rw [targetEq] at kept
  exact kept

/-- An actual whole-builder return must pass its real capacity loop and
reach the original current table allocation; a short stopped-cost branch
cannot stand in for this normal-return data. -/
theorem capacity_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (small : count<2^31) (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ selected inner bits,2≤bits ∧ bits≤32 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧
      selected.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      LocalEffects.erase selected=LocalEffects.erase source ∧ source.clock-selected.clock≤30 ∧
      (∀ name : MlS,ofString "cap"≠name → selected.locals.lookup name=source.locals.lookup name) ∧
      evaluateHOLFiniteState selected allocatedTail=(some (.returned value),inner) ∧ post=restore source "cap" inner := by
  rw [body_shape] at run
  obtain ⟨inner,continued,endpoint⟩ := Input.declaration_return_word source post "cap" (.const 4#64) 4#64 _ value rfl run
  let initial := bind source "cap" 4#64
  have safe : LocalPrefix (ofString "n") Constructor.capacityLoop := by
    rw [Capacity.loop_shape]
    exact .loop _ (.assign (ofString "cap") _ (by decide))
  obtain ⟨selected,normal,afterCap⟩ := sequence_returned initial inner Constructor.capacityLoop allocatedTail value (safe.summary_full initial).2.1 continued
  obtain ⟨bits,lower,upper,sufficient,capBound,cap,frame,price,others⟩ := capacity_normal initial selected count small
    ((bind_lookup_other source "cap" "n" 4#64 (by decide)).trans countCell) (bind_lookup_same _ _ _) normal
  refine ⟨selected,inner,bits,lower,upper,sufficient,capBound,cap,frame,price,?_,afterCap,endpoint⟩
  intro name different
  exact (others name different).trans (by simp [initial,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different])

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.capacity_normal
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.capacity_returned
