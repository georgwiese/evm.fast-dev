import InitECandidate.Solver.Rlp.ListCountAdvance

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values (pointer+offset) (length-offset)) := by
  simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,view.pointerCell,view.lengthCell,view.offsetCell,
    valueIsWord,valueWord,wordOpHOL,wordOp]

theorem arguments_fit (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) :
    (pointer+offset).toNat+(length-offset).toNat<2^64 := by
  have remaining := BitVec.toNat_sub_of_le view.bounded
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by have := view.fits; have := view.bounded; omega)
  rw [remaining,number]
  have := view.fits
  have := view.bounded
  omega

theorem loop_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤28*(length.toNat-offset.toNat)+31 := by
  have actual := ItemTotal.scoped_cost source (pointer+offset) (length-offset) cursor limit "total" arguments advance
    (arguments_read source pointer length cursor limit offset count view) view.arena (arguments_fit source pointer length cursor limit offset count view)
    installed (advance_price source.code)
  rwa [BitVec.toNat_sub_of_le view.bounded] at actual

theorem loop_body_safe : Input.LocalPrefix (ofString "p") loopBody :=
  .decCall _ _ _ _ (by decide) (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))

/-- Actual list iteration: derive its real positive total, both assignments,
retained arena, nonwrapping offset and cost in consumed bytes. -/
theorem loop_body_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ size : BitVec 64,1≤size.toNat ∧ size.toNat≤(length-offset).toNat ∧
      View target pointer length cursor limit (offset+size) (count+1#64) ∧
      (offset+size).toNat=offset.toNat+size.toNat ∧ source.clock-target.clock≤59*size.toNat := by
  obtain ⟨positive,calleePost,size,inner,advances,bounded,nextArena,priced,continuation,restored⟩ :=
    ItemTotal.scoped_none source target (pointer+offset) (length-offset) cursor limit "total" arguments advance
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
  exact ⟨size,advances,bounded,targetView,number,by rw [clockEq]; exact priced⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.arguments_read
#print axioms InitECandidate.Solver.Rlp.ListCount.arguments_fit
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_body_price
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_body_safe
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_body_none
