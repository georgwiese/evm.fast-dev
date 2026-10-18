import InitECandidate.Solver.GasBudget.StateFreshTxProgram
import Mathlib.Data.Fintype.Option

namespace InitECandidate.Solver.GasBudget.StateFreshTx

def Added : Nat → Type → Type
  | 0, ι => ι
  | n + 1, ι => Added n (Option ι)

def embed : (count : Nat) → {ι : Type} → ι → Added count ι
  | 0, _, index => index
  | count + 1, _, index => embed count (some index)

theorem embed_injective (count : Nat) {ι : Type} : Function.Injective (@embed count ι) := by
  induction count generalizing ι with
  | zero => exact fun _ _ same => same
  | succ count ih =>
    intro first second same
    have indices := ih same
    exact Option.some.inj indices

@[instance_reducible] def addedFintype (count : Nat) (ι : Type) [Fintype ι] : Fintype (Added count ι) := by
  induction count generalizing ι with
  | zero => change Fintype ι; exact inferInstance
  | succ count ih => exact ih (Option ι)

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.embed_injective
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.addedFintype
