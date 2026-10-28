import InitECandidate.Solver.Rlp.CurrentListCount.State
import InitECandidate.Solver.Rlp.ListCountAssignment

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Actual positive consumed bytes justify both real increments without
word wrap and retain the current initialized arenas and original input extent. -/
theorem advance_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count size : BitVec 64)
    (view : View source pointer length offset count) (positive : 1≤size.toNat)
    (bounded : size.toNat≤(length-offset).toNat) :
    View (ListCount.advancePost source offset count size) pointer length (offset+size) (count+1#64) ∧
      (offset+size).toNat=offset.toNat+size.toNat := by
  have remaining : (length-offset).toNat=length.toNat-offset.toNat := BitVec.toNat_sub_of_le view.bounded
  have lengthBound:=length.isLt
  have offsetNumber : (offset+size).toNat=offset.toNat+size.toNat := BitVec.toNat_add_of_lt (by omega)
  have countNumber : (count+1#64).toNat=count.toNat+1 := BitVec.toNat_add_of_lt (by change count.toNat+1<2^64; have h:=view.counted; omega)
  refine ⟨⟨view.arena.of_frame rfl,?_,?_,?_,?_,?_,?_,view.fits⟩,offsetNumber⟩
  · rw [ListCount.advancePost,bind_lookup_other _ "count" "p" _ (by decide),bind_lookup_other _ "off" "p" _ (by decide)]
    exact view.pointerCell
  · rw [ListCount.advancePost,bind_lookup_other _ "count" "len" _ (by decide),bind_lookup_other _ "off" "len" _ (by decide)]
    exact view.lengthCell
  · rw [ListCount.advancePost,bind_lookup_other _ "count" "off" _ (by decide)]
    exact bind_lookup_same _ _ _
  · exact bind_lookup_same _ _ _
  · rw [offsetNumber,countNumber]
    have h:=view.counted
    omega
  · rw [offsetNumber]
    omega

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.advance_view
