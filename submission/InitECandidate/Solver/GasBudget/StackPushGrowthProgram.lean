import InitECandidate.Solver.GasBudget.StackPushProgram
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.Arenas.Calls

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def growGuard : ProgHOL 64 := .ite (.cmp .notLower (localVar "cap") (.const 1024#64))
  (.raise (ofString "EvmErr") (.const 3#64)) .skip
def growClamp : ProgHOL 64 := .ite (.cmp .lower (.const 1024#64) (localVar "ncap"))
  (.assign .local (ofString "ncap") (.const 1024#64)) .skip
def growStores : ProgHOL 64 := .seq (.store (frameAddress 8#64) (localVar "ns"))
  (.store (frameAddress 232#64) (localVar "ncap"))
def growCopy : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
  [localVar "ns", frameLoad 8#64, .panop .mul [localVar "sp", .const 32#64]]
def growAllocate : ProgHOL 64 := .decCall (ofString "ns") .one (ofString "scratch_alloc")
  [.panop .mul [localVar "ncap", .const 32#64]] (.seq growCopy growStores)

theorem grow_branch_shape : growBranch = .seq growGuard
    (.dec (ofString "ncap") .one (.panop .mul [localVar "cap", .const 2#64]) (.seq growClamp growAllocate)) := by
  simp only [growBranch, growth, afterCap, afterSP, body, Guest.guestFn_stack_push,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    growGuard, growClamp, growAllocate, growCopy, growStores, localVar, frameAddress, frameLoad]

/-- Reachable doubling capacities make the real clamp a no-op. The positive
capacity premise is needed to establish free space after growth. -/
theorem grow_numbers (capacity : BitVec 64) (positive : 0 < capacity.toNat) (bounded : capacity.toNat ≤ 512) :
    (capacity * 2#64).toNat = 2 * capacity.toNat ∧
    capacity.toNat < (capacity * 2#64).toNat ∧ (capacity * 2#64).toNat ≤ 1024 ∧
    ((capacity * 2#64) * 32#64).toNat = 64 * capacity.toNat ∧
    (capacity * 32#64).toNat = 32 * capacity.toNat := by
  have doubled : (capacity * 2#64).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul]
    change (capacity.toNat * 2) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have allocation : ((capacity * 2#64) * 32#64).toNat = 64 * capacity.toNat := by
    rw [BitVec.toNat_mul, doubled]
    change (2 * capacity.toNat * 32) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have copied : (capacity * 32#64).toNat = 32 * capacity.toNat := by
    rw [BitVec.toNat_mul]
    change (capacity.toNat * 32) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨doubled, by omega, by omega, allocation, copied⟩

/-- The actual aligned memcpy copies four words per loop iteration, so a
full stack growth copies capacity slots at exactly capacity body clocks. -/
theorem grow_copy_price (source destination : BitVec 64) (capacity : Nat)
    (aligned : WitnessRadix.CopyGeneral.aligned source destination) :
    WitnessRadix.CopyGeneral.cost source destination (32 * capacity) = capacity := by
  simp [WitnessRadix.CopyGeneral.cost, aligned, WitnessRadix.CopyWords.prefixCost,
    WitnessRadix.CopyWords.prefixIndex, WitnessRadix.CopyBytes.suffixCost, Nat.mul_comm]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_branch_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_numbers
#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_copy_price
