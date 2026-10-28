import InitECandidate.Solver.Rlp.CurrentListCount.Body
import InitECandidate.Solver.Rlp.CurrentItemTotalCallEncoding
import InitECandidate.Solver.Rlp.ListItems

namespace InitECandidate.Solver.Rlp.CurrentListCount
open ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real continuing count iteration derives its actual encoded item,
positive nonwrapping advance, retained memory frame and paid byte cost. -/
theorem loop_body_encoding (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ item : ListItem,item.valid ∧ Header.Encoded source (pointer+offset) item.header item.payload item.flag ∧
      item.size≤(length-offset).toNat ∧ View target pointer length (offset+item.total) (count+1#64) ∧
      (offset+item.total).toNat=offset.toNat+item.size ∧ (count+1#64).toNat=count.toNat+1 ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤45*item.size := by
  obtain ⟨positive,calleePost,header,payload,flag,inner,valid,encoding,frame,priced,continuation,restored⟩ :=
    CurrentItemTotal.scoped_none_encoding source target (pointer+offset) (length-offset) "total" arguments advance
      (arguments_read source pointer length offset count view) view.arena (arguments_fit source pointer length offset count view) installed normal
  obtain ⟨head,advances,bounded,binary,listHead⟩ := Header.Valid.result_fields (length-offset).toNat header payload flag valid
  let item : ListItem := ⟨header,payload,flag⟩
  have itemValid : item.valid := ⟨header,payload,flag,rfl,head,advances,Nat.le_refl _,binary,listHead⟩
  have sizeBound : item.size≤(length-offset).toNat := bounded
  have sizePositive : 1≤item.size := advances
  have totalNumber : item.total.toNat=item.size := BitVec.toNat_add_of_lt (by have := (length-offset).isLt; change header.toNat+payload.toNat<2^64; omega)
  let ready := bind {calleePost with locals:=source.locals} "total" item.total
  have readyView : View ready pointer length offset count :=
    ⟨view.arena.of_frame frame,
      (bind_lookup_other _ "total" "p" _ (by decide)).trans view.pointerCell,
      (bind_lookup_other _ "total" "len" _ (by decide)).trans view.lengthCell,
      (bind_lookup_other _ "total" "off" _ (by decide)).trans view.offsetCell,
      (bind_lookup_other _ "total" "count" _ (by decide)).trans view.countCell,
      view.counted,view.bounded,view.fits⟩
  have execution := advance_execute ready offset count item.total readyView.offsetCell readyView.countCell (bind_lookup_same _ _ _)
  change evaluateHOLFiniteState ready advance=(none,inner) at continuation
  rw [execution] at continuation
  have innerEq : inner=advancePost ready offset count item.total := (Prod.mk.inj continuation).2.symm
  rw [innerEq] at restored
  obtain ⟨advanced,number⟩ := advance_view ready pointer length offset count item.total readyView
    (by rw [totalNumber]; exact sizePositive) (by rw [totalNumber]; exact sizeBound)
  rw [totalNumber] at number
  have targetView := advanced.restored source
  rw [←restored] at targetView
  have countNumber : (count+1#64).toNat=count.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change count.toNat+1<2^64; have := (count+1#64).isLt; have := view.counted; have := view.bounded; have := length.isLt; have remaining := BitVec.toNat_sub_of_le view.bounded; rw [remaining] at sizeBound; omega)]
    rfl
  have clockEq : target.clock=calleePost.clock := by rw [restored]; rfl
  refine ⟨item,itemValid,encoding,sizeBound,targetView,number,countNumber,?_,?_⟩
  · rw [restored]
    exact frame
  · rw [clockEq]
    change source.clock-calleePost.clock≤45*item.total.toNat at priced
    rwa [totalNumber] at priced

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.loop_body_encoding
