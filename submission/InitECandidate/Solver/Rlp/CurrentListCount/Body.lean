import InitECandidate.Solver.Rlp.CurrentListCount.Advance

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) ListCount.arguments=some (Header.values (pointer+offset) (length-offset)) := by
  simp [ListCount.arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,view.pointerCell,view.lengthCell,view.offsetCell,
    valueIsWord,valueWord,wordOpHOL,wordOp]

theorem arguments_fit (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) : (pointer+offset).toNat+(length-offset).toNat<2^64 := by
  have remaining:=BitVec.toNat_sub_of_le view.bounded
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by have a:=view.fits; have b:=view.bounded; omega)
  rw [remaining,number]
  have a:=view.fits; have b:=view.bounded
  omega

theorem loop_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) :
    source.clock-(evaluateHOLFiniteState source ListCount.loopBody).2.clock≤28*(length.toNat-offset.toNat)+31 := by
  have paid:=CurrentItemTotal.scoped_cost source (pointer+offset) (length-offset) view.arena (arguments_fit source pointer length offset count view)
    (ofString "total") ListCount.arguments ListCount.advance 0 (arguments_read source pointer length offset count view) (ListCount.advance_price source.code)
  rwa [BitVec.toNat_sub_of_le view.bounded] at paid

theorem loop_body_safe : LocalPrefix (ofString "p") ListCount.loopBody :=
  .decCall _ _ _ _ (by decide) (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))

/-- Each actual continuing iteration derives its own positive consumed-byte
advance, exact two assignments and cost in those bytes. The same real caller
retains original input, initialized arenas and every nonlocal observation. -/
theorem loop_body_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) (normal : evaluateHOLFiniteState source ListCount.loopBody=(none,post)) :
    ∃ size : BitVec 64,1≤size.toNat ∧ size.toNat≤(length-offset).toNat ∧
      View post pointer length (offset+size) (count+1#64) ∧ (offset+size).toNat=offset.toNat+size.toNat ∧
      source.clock-post.clock≤59*size.toNat ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      Validation.Outside source post 2952790016 2965299200 := by
  obtain ⟨size,paid,calleePost,inner,positive,bounded,minimum,maximum,spent,clock,metadata,outside,continuation,endpoint⟩ := CurrentItemTotal.scoped_none source post (pointer+offset) (length-offset)
    view.arena (arguments_fit source pointer length offset count view) "total" ListCount.arguments ListCount.advance (arguments_read source pointer length offset count view) normal
  let ready:=bind {calleePost with locals:=source.locals} "total" size
  have readyView : View ready pointer length offset count := (view.at_caller calleePost metadata).bound "total" size (by decide)
  have execution:=ListCount.advance_execute ready offset count size readyView.offsetCell readyView.countCell (bind_lookup_same _ _ _)
  rw [execution] at continuation
  have innerEq : inner=ListCount.advancePost ready offset count size := (Prod.mk.inj continuation).2.symm
  rw [innerEq] at endpoint
  obtain ⟨advanced,number⟩ := advance_view ready pointer length offset count size readyView positive bounded
  have targetView:=advanced.restored source
  rw [←endpoint] at targetView
  have clockEq : post.clock=calleePost.clock := by rw [endpoint]; rfl
  refine ⟨size,positive,bounded,targetView,number,?_,?_,?_⟩
  · rw [clockEq,clock]
    omega
  · rw [endpoint]
    exact metadata
  · refine ⟨?_,?_⟩
    · rw [endpoint]
      exact outside.runtime
    · intro query outsideQuery
      rw [endpoint]
      exact outside query outsideQuery

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.arguments_read
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.arguments_fit
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.loop_body_price
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.loop_body_none
