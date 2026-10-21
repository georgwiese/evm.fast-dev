import InitECandidate.Solver.Input.FrozenWitnessDatabases
import InitECandidate.Solver.Mpt.WitnessCoreResolveState

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem FrozenWitnessDatabases.hash_state (input : Guest.InputBlob)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (record db hash : BitVec 64)
    (data : Mpt.WitnessRecord.Description) (frozen : FrozenWitnessDatabases input source frontier)
    (view : Mpt.WitnessRecord.View source record db data) :
    FrozenWitnessDatabases input (Mpt.WitnessCore.hashState source record hash) frontier := by
  apply frozen.frame input source (Mpt.WitnessCore.hashState source record hash) frontier rfl rfl rfl
  intro query lower upper
  have number : (record+80#64).toNat=record.toNat+80:=by
    simpa only [byteAddress] using byteAddress_toNat record 80 (by have upper:=view.arena.upper; omega)
  have away : query≠record+80#64:=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    have bound:=view.ceiling
    omega
  exact if_neg away

/-- The actual resolver's terminal continuation stores only its pending
hash field in scratch and updates result/mode locals; both fixed databases
survive at their original frontier. -/
theorem FrozenWitnessDatabases.resolved_terminal (input : Guest.InputBlob)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (record db node : BitVec 64)
    (data : Mpt.WitnessRecord.Description) (frozen : FrozenWitnessDatabases input source frontier)
    (view : Mpt.WitnessRecord.View source record db data) :
    FrozenWitnessDatabases input (Mpt.WitnessCore.resolvedTerminal source record node) frontier := by
  have changed:=frozen.hash_state input source frontier record db 0#64 data view
  exact changed.frame input _ (Mpt.WitnessCore.resolvedTerminal source record node) frontier rfl rfl
    (Mpt.WitnessCore.resolved_terminal_other source record node "db" (by decide) (by decide)) (by intros; rfl)

/-- The actual preimage continuation keeps the immutable databases while
installing the next bounded decode slice and pending hash. -/
theorem FrozenWitnessDatabases.resolved_decode (input : Guest.InputBlob)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (record db pointer length hash : BitVec 64)
    (data : Mpt.WitnessRecord.Description) (frozen : FrozenWitnessDatabases input source frontier)
    (view : Mpt.WitnessRecord.View source record db data) :
    FrozenWitnessDatabases input (Mpt.WitnessCore.resolvedDecode source record pointer length hash) frontier := by
  have changed:=frozen.hash_state input source frontier record db hash data view
  exact changed.frame input _ (Mpt.WitnessCore.resolvedDecode source record pointer length hash) frontier rfl rfl
    (Mpt.WitnessCore.resolved_decode_other source record pointer length hash "db" (by decide) (by decide) (by decide)) (by intros; rfl)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.hash_state
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.resolved_terminal
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.resolved_decode
