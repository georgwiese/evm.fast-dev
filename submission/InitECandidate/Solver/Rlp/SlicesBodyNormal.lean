import InitECandidate.Solver.Rlp.SlicesStoreFrame
import InitECandidate.Solver.Rlp.UncheckedCall
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def bodyPost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array index offset size : BitVec 64) (paid : Nat) :=
  restore source "total" (storesPost (bind {source with clock:=source.clock-paid} "total" size) pointer array index offset size)

theorem body_post_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array index offset count size : BitVec 64) (paid : Nat) (view : Locals source pointer array index offset count) :
    Locals (bodyPost source pointer array index offset size paid) pointer array (index+1#64) (offset+size) count := by
  have ready : Locals (bind {source with clock:=source.clock-paid} "total" size) pointer array index offset count :=
    ⟨(bind_lookup_other _ "total" "p" _ (by decide)).trans view.pointerCell,
      (bind_lookup_other _ "total" "arr" _ (by decide)).trans view.arrayCell,
      (bind_lookup_other _ "total" "i" _ (by decide)).trans view.indexCell,
      (bind_lookup_other _ "total" "off" _ (by decide)).trans view.offsetCell,
      (bind_lookup_other _ "total" "count" _ (by decide)).trans view.countCell⟩
  have advanced := stores_post_locals _ pointer array index offset count size ready
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (restore_lookup_other source _ "total" "p" (by decide)).trans advanced.pointerCell
  · exact (restore_lookup_other source _ "total" "arr" (by decide)).trans advanced.arrayCell
  · exact (restore_lookup_other source _ "total" "i" (by decide)).trans advanced.indexCell
  · exact (restore_lookup_other source _ "total" "off" (by decide)).trans advanced.offsetCell
  · exact (restore_lookup_other source _ "total" "count" (by decide)).trans advanced.countCell

/-- An actual normal original second-pass iteration recovers the encoded
item's exact total, both genuine writes and complete reached state. -/
theorem loop_body_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array index offset count : BitVec 64) (item : ListItem)
    (view : Locals source pointer array index offset count)
    (encoding : Header.Encoded source (pointer+offset) item.header item.payload item.flag)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ paid,1≤paid ∧ paid≤10 ∧ paid≤source.clock ∧ target=bodyPost source pointer array index offset item.total paid := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [.op .add [localVar "p",localVar "off"]]=some (Unchecked.values (pointer+offset)) := by
    simp [Unchecked.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,view.pointerCell,view.offsetCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨paid,inner,positive,bounded,funded,continuation,restored⟩ :=
    Unchecked.scoped_none_item source target (pointer+offset) item "total" _ stores args encoding installed normal
  let ready := bind {source with clock:=source.clock-paid} "total" item.total
  have readyView : Locals ready pointer array index offset count :=
    ⟨(bind_lookup_other _ "total" "p" _ (by decide)).trans view.pointerCell,
      (bind_lookup_other _ "total" "arr" _ (by decide)).trans view.arrayCell,
      (bind_lookup_other _ "total" "i" _ (by decide)).trans view.indexCell,
      (bind_lookup_other _ "total" "off" _ (by decide)).trans view.offsetCell,
      (bind_lookup_other _ "total" "count" _ (by decide)).trans view.countCell⟩
  obtain ⟨firstMapped,secondMapped,innerEq⟩ := stores_none ready inner pointer array index offset count item.total readyView (bind_lookup_same _ _ _) continuation
  rw [innerEq] at restored
  exact ⟨paid,positive,bounded,funded,restored⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.body_post_locals
#print axioms InitECandidate.Solver.Rlp.Slices.loop_body_none
