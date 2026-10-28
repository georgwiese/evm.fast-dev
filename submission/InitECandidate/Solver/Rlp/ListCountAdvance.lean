import InitECandidate.Solver.Rlp.ListCountAssignment
import InitECandidate.Solver.Rlp.ListCountProgram

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem advance_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count size : BitVec 64)
    (view : View source pointer length cursor limit offset count) (positive : 1≤size.toNat)
    (bounded : size.toNat≤(length-offset).toNat) :
    View (advancePost source offset count size) pointer length cursor limit (offset+size) (count+1#64) ∧
      (offset+size).toNat=offset.toNat+size.toNat := by
  have remaining : (length-offset).toNat=length.toNat-offset.toNat := BitVec.toNat_sub_of_le view.bounded
  have lengthBound := length.isLt
  have offsetNumber : (offset+size).toNat=offset.toNat+size.toNat := BitVec.toNat_add_of_lt (by omega)
  have countNumber : (count+1#64).toNat=count.toNat+1 := BitVec.toNat_add_of_lt (by change count.toNat+1<2^64; have := view.counted; omega)
  refine ⟨⟨Validation.Arena.of_fields source _ cursor limit view.arena rfl rfl,?_,?_,?_,?_,?_,?_,view.fits⟩,offsetNumber⟩
  · rw [advancePost,bind_lookup_other _ "count" "p" _ (by decide),bind_lookup_other _ "off" "p" _ (by decide)]
    exact view.pointerCell
  · rw [advancePost,bind_lookup_other _ "count" "len" _ (by decide),bind_lookup_other _ "off" "len" _ (by decide)]
    exact view.lengthCell
  · rw [advancePost,bind_lookup_other _ "count" "off" _ (by decide)]
    exact bind_lookup_same _ _ _
  · exact bind_lookup_same _ _ _
  · rw [offsetNumber,countNumber]
    have := view.counted
    omega
  · rw [offsetNumber]
    omega

theorem View.restored (source saved : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) :
    View (restore saved "total" source) pointer length cursor limit offset count :=
  ⟨Validation.Arena.of_fields source _ cursor limit view.arena rfl rfl,
    (restore_lookup_other saved source "total" "p" (by decide)).trans view.pointerCell,
    (restore_lookup_other saved source "total" "len" (by decide)).trans view.lengthCell,
    (restore_lookup_other saved source "total" "off" (by decide)).trans view.offsetCell,
    (restore_lookup_other saved source "total" "count" (by decide)).trans view.countCell,
    view.counted,view.bounded,view.fits⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.advance_view
#print axioms InitECandidate.Solver.Rlp.ListCount.View.restored
