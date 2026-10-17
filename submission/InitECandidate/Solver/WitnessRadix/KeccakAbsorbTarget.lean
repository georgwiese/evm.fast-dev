import InitECandidate.Solver.WitnessRadix.KeccakAbsorbExecution

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

theorem hashControl_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (clock : Nat) :
    hashControl { source with clock := clock } = hashControl source := rfl

theorem hashControl_empty {F : Type} (source : PanSemStateFiniteExact 64 F) :
    hashControl (emptyLocalsHOLFinite source) = hashControl source := rfl

theorem hashControl_restore {F : Type} (saved source : PanSemStateFiniteExact 64 F) (name : String) :
    hashControl (restore saved name source) = hashControl source := rfl

theorem target_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) (bytes : List (BitVec 8)) :
    (target source stp blk bytes).clock = source.clock-18 := rfl

theorem target_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) (bytes : List (BitVec 8)) :
    hashControl (target source stp blk bytes) = hashControl source := by
  rw [target,hashControl_restore,hashControl_empty,after,hashControl_clock,permutation_control]
  exact hashControl_of_control (bind source "i" 0#64) (prepared source stp blk)
    (stateLanes_control _ _ _ _ _)

def Away (stp query : BitVec 64) : Prop :=
  (∀ word : Fin 25, query ≠ byteAddress stp (8*word.val)) ∧
  (∀ offset < 200, query ≠ panByteAlignHOL (width := 64) (byteAddress stp offset))

theorem target_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk query : BitVec 64) (bytes : List (BitVec 8))
    (away : Away stp query) : (target source stp blk bytes).memory query = source.memory query := by
  change (Keccak.post (prepared source stp blk) stp bytes).memory query = source.memory query
  rw [Keccak.post_memory_away _ _ _ _ away.2]
  apply stateLanes_memory_away
  intro offset low high
  exact away.1 ⟨offset,by omega⟩

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.hashControl_clock
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.hashControl_empty
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.hashControl_restore
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.target_clock
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.target_control
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.target_memory_away
