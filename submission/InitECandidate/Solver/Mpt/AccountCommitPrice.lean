import InitECandidate.Solver.GasBudget.JournalAppendSetPrice

namespace InitECandidate.Solver.Mpt.AccountCommit
open MutableTable

theorem account_set_price (population : Nat) : GasBudget.Journal.Append.setPrice .account population = 17 * population + 37 := by
  simp [GasBudget.Journal.Append.setPrice,Get.bodyPrice,Set.noGrowthPrice,Insert.findPrice,Insert.rawPrice,
    Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price]
  omega

theorem account_set_price_mono (first second : Nat) (ordered : first ≤ second) :
    GasBudget.Journal.Append.setPrice .account first ≤ GasBudget.Journal.Append.setPrice .account second := by
  rw [account_set_price,account_set_price]
  omega

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.account_set_price
#print axioms InitECandidate.Solver.Mpt.AccountCommit.account_set_price_mono
