import InitECandidate.Solver.Input.CopyLoop
import InitECandidate.Solver.Input.CopyWalkState

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def copyRounds (length : Nat) : Nat := (length+7)/8

theorem copyRounds_bounds (length : Nat) :
    length≤8*copyRounds length ∧ 8*copyRounds length<length+8 ∧ copyRounds length≤134217726 ∨ Guest.maxInputBytes<length := by
  dsimp [copyRounds]
  change length≤8*((length+7)/8) ∧ 8*((length+7)/8)<length+8 ∧ (length+7)/8≤134217726 ∨ 1073741808<length
  omega

theorem copyRounds_fit (length : Nat) (bounded : length≤Guest.maxInputBytes) :
    length≤8*copyRounds length ∧ 8*copyRounds length<length+8 ∧ copyRounds length≤134217726 := by
  have h:=copyRounds_bounds length
  omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copyRounds_bounds
#print axioms InitECandidate.Solver.Input.Blob.copyRounds_fit
