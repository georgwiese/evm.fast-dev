import InitECandidate.Solver.Input.FrozenWitnessDatabases
import InitECandidate.Solver.Mpt.WitnessCorePush

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The actual core PREV-link push retains both witness databases at their
fixed entry frontier, while preserving the new record's complete view. -/
theorem FrozenWitnessDatabases.pushed (input : Guest.InputBlob)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (record db previous : BitVec 64)
    (data : Mpt.WitnessRecord.Description) (frozen : FrozenWitnessDatabases input source frontier)
    (view : Mpt.WitnessRecord.View source record db data) :
    FrozenWitnessDatabases input (Mpt.WitnessCore.pushed source record previous data.payload) frontier := by
  apply frozen.frame input source (Mpt.WitnessCore.pushed source record previous data.payload) frontier rfl rfl
    (Mpt.WitnessCore.pushed_other source record previous data.payload "db" (by decide) (by decide) (by decide))
  intro query lower upper
  have away : query≠record:=by
    intro same
    subst query
    have bound:=view.ceiling
    omega
  exact if_neg away

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.pushed
