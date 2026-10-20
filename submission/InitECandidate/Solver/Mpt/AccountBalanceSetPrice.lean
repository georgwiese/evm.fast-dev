import InitECandidate.Solver.Mpt.AccountBalanceSetResult

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open MutableTable GasBudget

theorem get_price_mono (kind : KeyHash.Kind) (first second : Nat) (ordered : first ≤ second) :
    Get.bodyPrice kind first ≤ Get.bodyPrice kind second := by
  unfold Get.bodyPrice
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ ordered) _

theorem delete_price_mono (kind : KeyHash.Kind) (first second : Nat) (ordered : first ≤ second) :
    Journal.Append.deletePrice kind first ≤ Journal.Append.deletePrice kind second := by
  have get := get_price_mono kind first second ordered
  have find : Insert.findPrice kind first ≤ Insert.findPrice kind second := by
    unfold Insert.findPrice
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ ordered) _
  have scan := Nat.mul_le_mul_left (Delete.scanPrice kind) (Nat.sub_le_sub_right ordered 1)
  unfold Journal.Append.deletePrice Journal.Append.deleteSuffixPrice Delete.modelPrice Delete.tailPrice
  omega

theorem suffix_price_mono (markers outers accounts bound : Nat)
    (markersBound : markers ≤ bound) (outersBound : outers ≤ bound) (accountsBound : accounts ≤ bound)
    (destroyed found : Bool) (iterations : Nat) :
    suffixPrice markers outers accounts destroyed found iterations ≤ suffixPrice bound bound bound destroyed found iterations := by
  have set1 := AccountCommit.account_set_price_mono accounts bound accountsBound
  have set2 := AccountCommit.account_set_price_mono (accounts + 1) (bound + 1) (by omega)
  have get := get_price_mono .account outers bound outersBound
  have delete := delete_price_mono .account outers bound outersBound
  have loop := DestroyStorage.loop_price_mono markers bound iterations markersBound
  cases destroyed <;> cases found <;> simp only [suffixPrice,Bool.false_eq_true,↓reduceIte] <;> omega

def wholePrice (population : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  43 * population + 31152 + suffixPrice (population + 3) (population + 3) (population + 3) destroyed found iterations

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.get_price_mono
#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.delete_price_mono
#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.suffix_price_mono
