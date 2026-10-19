import InitECandidate.Solver.Rlp.ListCountBody
import InitECandidate.Solver.Rlp.ItemTotalCallFrame

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual list iteration: derive its real positive total, both assignments,
retained arena, nonwrapping offset and cost in consumed bytes. -/
theorem loop_body_none_above (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ size : BitVec 64,1≤size.toNat ∧ size.toNat≤(length-offset).toNat ∧
      View target pointer length cursor limit (offset+size) (count+1#64) ∧
      (offset+size).toNat=offset.toNat+size.toNat ∧ Validation.Above source target cursor.toNat ∧ source.clock-target.clock≤59*size.toNat := by
  obtain ⟨positive,calleePost,size,inner,advances,bounded,nextArena,above,priced,continuation,restored⟩ :=
    ItemTotal.scoped_none_above source target (pointer+offset) (length-offset) cursor limit "total" arguments advance
      (arguments_read source pointer length cursor limit offset count view) view.arena (arguments_fit source pointer length cursor limit offset count view) installed normal
  let ready := bind {calleePost with locals:=source.locals} "total" size
  have readyView : View ready pointer length cursor limit offset count :=
    ⟨Validation.Arena.of_fields calleePost ready cursor limit nextArena rfl rfl,
      (bind_lookup_other _ "total" "p" _ (by decide)).trans view.pointerCell,
      (bind_lookup_other _ "total" "len" _ (by decide)).trans view.lengthCell,
      (bind_lookup_other _ "total" "off" _ (by decide)).trans view.offsetCell,
      (bind_lookup_other _ "total" "count" _ (by decide)).trans view.countCell,
      view.counted,view.bounded,view.fits⟩
  have execution := advance_execute ready offset count size readyView.offsetCell readyView.countCell (bind_lookup_same _ _ _)
  rw [execution] at continuation
  have innerEq : inner=advancePost ready offset count size := (Prod.mk.inj continuation).2.symm
  rw [innerEq] at restored
  obtain ⟨advanced,number⟩ := advance_view ready pointer length cursor limit offset count size readyView advances bounded
  have targetView := View.restored _ source pointer length cursor limit (offset+size) (count+1#64) advanced
  rw [←restored] at targetView
  have clockEq : target.clock=calleePost.clock := by rw [restored]; rfl
  refine ⟨size,advances,bounded,targetView,number,?_,by rw [clockEq]; exact priced⟩
  intro query upper
  rw [restored]
  exact above query upper

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.loop_body_none_above
