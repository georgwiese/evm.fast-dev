import InitECandidate.Solver.MutableTable.GetModelExecution
import InitECandidate.Solver.MutableTable.SetNoGrowthExecution

namespace InitECandidate.Solver.GasBudget.Journal.Append
open MutableTable

def setPrice (kind : KeyHash.Kind) (population : Nat) : Nat :=
  Get.bodyPrice kind population + 1 + (KeyHash.keySize kind + 2) + Set.noGrowthPrice kind population + 1

end InitECandidate.Solver.GasBudget.Journal.Append
