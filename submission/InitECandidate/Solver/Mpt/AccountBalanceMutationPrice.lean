import InitECandidate.Solver.Mpt.AccountBalanceMutationFamily
import InitECandidate.Solver.Mpt.AccountBalanceSetPrice

namespace InitECandidate.Solver.Mpt.AccountBalanceSet

theorem commit_price_mono (markers outers accounts bound : Nat)
    (markersBound : markers ≤ bound) (outersBound : outers ≤ bound) (accountsBound : accounts ≤ bound)
    (destroyed found : Bool) (iterations : Nat) :
    commitPrice markers outers accounts destroyed found iterations ≤ commitPrice bound bound bound destroyed found iterations :=
  Nat.sub_le_sub_right (suffix_price_mono markers outers accounts bound markersBound outersBound accountsBound destroyed found iterations) 7

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.commit_price_mono
