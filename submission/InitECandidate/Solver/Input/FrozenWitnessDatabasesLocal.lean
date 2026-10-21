import InitECandidate.Solver.Input.FrozenWitnessDatabases
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem FrozenWitnessDatabases.bind (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (frozen : FrozenWitnessDatabases input source frontier) (name : String) (word : BitVec 64)
    (notDb : ofString name≠ofString "db") : FrozenWitnessDatabases input (QueryBranch.bind source name word) frontier :=
  frozen.frame input source (QueryBranch.bind source name word) frontier rfl rfl (bind_lookup_other source name "db" word notDb) (fun _ _ _=>rfl)

theorem FrozenWitnessDatabases.restore (input : Guest.InputBlob) (saved source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (frozen : FrozenWitnessDatabases input source frontier) (name : String)
    (notDb : ofString name≠ofString "db") : FrozenWitnessDatabases input (QueryBranch.restore saved name source) frontier :=
  frozen.frame input source (QueryBranch.restore saved name source) frontier rfl rfl (ScalarScope.restore_other saved source name "db" notDb) (fun _ _ _=>rfl)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.bind
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.restore
