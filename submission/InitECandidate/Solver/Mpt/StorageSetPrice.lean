import InitECandidate.Solver.Mpt.StorageSetNormal
import InitECandidate.Solver.Mpt.AccountCommitPrice

namespace InitECandidate.Solver.Mpt.StorageSet
open MutableTable GasBudget

theorem whole_price_exact (population : Nat) (created : Bool) :
    wholePrice population created = if created then 68 * population + 31322 else 64 * population + 31263 := by
  have constructor : TableRuntime.price 8 = 8 := rfl
  have getter : Get.bodyPrice .account (population + 3) = 8 * (population + 3) + 2 := by
    simp [Get.bodyPrice,Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price]
  cases created <;> simp [wholePrice,tailPrice,constructor,getter,AccountCommit.account_set_price,word_set_price] <;> omega

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.whole_price_exact
