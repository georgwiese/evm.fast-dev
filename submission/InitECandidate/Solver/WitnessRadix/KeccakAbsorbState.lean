import InitECandidate.Solver.WitnessRadix.KeccakAbsorbLoop

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

theorem stateLanes_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (unaligned : Bool) (lane rounds : Nat) :
    (stateLanes source stp unaligned lane rounds).clock = source.clock - rounds := by
  induction rounds generalizing source lane with
  | zero => rfl
  | succ rounds ih =>
    rw [stateLanes, ih]
    change source.clock - 1 - rounds = source.clock - (rounds+1)
    omega

theorem stateLanes_control {F : Type} (source : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (unaligned : Bool) (lane rounds : Nat) :
    CopyContext.control (stateLanes source stp unaligned lane rounds) = CopyContext.control source := by
  induction rounds generalizing source lane with
  | zero => rfl
  | succ rounds ih => exact ih _ (lane+1)

theorem stateLanes_other {F : Type} (source : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (unaligned : Bool) (lane rounds : Nat)
    (name : MlS) (different : ofString "i" ≠ name) :
    (stateLanes source stp unaligned lane rounds).locals.lookup name = source.locals.lookup name := by
  induction rounds generalizing source lane with
  | zero => rfl
  | succ rounds ih =>
    rw [stateLanes, ih, lane_other _ _ _ _ _ different]
    rfl

theorem stateLanes_domain {F : Type} (source : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (unaligned : Bool) (lane rounds : Nat) :
    (stateLanes source stp unaligned lane rounds).memaddrs = source.memaddrs := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memaddrs) (stateLanes_control source stp unaligned lane rounds)
  exact h

theorem stateLanes_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (stp query : BitVec 64) (unaligned : Bool) (lane rounds : Nat)
    (away : ∀ offset, lane ≤ offset → offset < lane+rounds → query ≠ byteAddress stp (8*offset)) :
    (stateLanes source stp unaligned lane rounds).memory query = source.memory query := by
  induction rounds generalizing source lane with
  | zero => rfl
  | succ rounds ih =>
    rw [stateLanes, ih _ (lane+1) (by intro offset low high; exact away offset (by omega) (by omega))]
    exact lane_memory_away _ _ _ _ _ (away lane (Nat.le_refl _) (by omega))

/-- Nonlocal fields preserved by hashing, allowing its actual event append. -/
def hashControl {F : Type} (source : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite { source with
    memory := (fun _ => .word 0#64)
    clock := 0
    ffi := { source.ffi with ioEvents := [] } }

theorem hashControl_of_control {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (same : CopyContext.control target = CopyContext.control source) : hashControl target = hashControl source := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with ffi := { state.ffi with ioEvents := [] } }) same
  exact h

theorem permutation_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp : BitVec 64) (bytes : List (BitVec 8)) :
    hashControl (Keccak.post source stp bytes) = hashControl source := by
  simp only [hashControl, Keccak.post, Keccak.nextFfi, emptyLocalsHOLFinite]

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_clock
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_control
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_other
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_domain
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.hashControl_of_control
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.permutation_control
