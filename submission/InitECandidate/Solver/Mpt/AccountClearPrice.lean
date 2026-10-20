import InitECandidate.Solver.Mpt.AccountBalanceMutationPrice
import InitECandidate.Solver.Mpt.DestroyStorageMutationResult

namespace InitECandidate.Solver.Mpt.AccountClear

def tailPrice (population : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  43 * population + 31152 + (7 + AccountBalanceSet.commitPrice (population + 3) (population + 3) (population + 3) destroyed found iterations)

def wholePrice (population : Nat) (foundStorage : Bool) (storageIterations : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  DestroyStorage.phasePrice population population foundStorage storageIterations + tailPrice (population + storageIterations) destroyed found iterations

end InitECandidate.Solver.Mpt.AccountClear
