import InitECandidate.Solver.GasBudget.GasSeed

namespace InitECandidate.Solver.GasBudget.FrameRank
open Flapjack

def phasePrice : Bool → Nat | false => 0 | true => 1

/-- Current-state rank for a live invocation. The empty list denotes final
root exit. Whole-run reachability and the actual opcode/suffix transitions
still need to instantiate the physical sum and phase premises below. -/
def value (limit : Nat) (memory : Memory) (live : List (BitVec 64)) (active : Bool) : Nat :=
  match live with
  | [] => 0
  | _ :: _ => 3 * (limit - FrameSums.used memory live) + 2 * live.length + phasePrice active

theorem charged (limit : Nat) (before after : Memory) (live next : List (BitVec 64)) (nextActive : Bool)
    (nonempty : live ≠ [])
    (credit : FrameSums.used before live + 1 ≤ FrameSums.used after next)
    (cap : FrameSums.used after next ≤ limit) (children : next.length ≤ live.length + 1) :
    value limit after next nextActive < value limit before live true := by
  cases live with
  | nil => exact (nonempty rfl).elim
  | cons head rest =>
    cases next with
    | nil => simp only [FrameSums.used, List.map_nil, List.sum_nil] at credit; omega
    | cons nextHead nextRest =>
      cases nextActive <;> simp only [value, phasePrice, List.length_cons]
      all_goals simp only [List.length_cons] at children
      all_goals omega

theorem terminal (limit : Nat) (before after : Memory) (live next : List (BitVec 64))
    (nonempty : live ≠ []) (monotone : FrameSums.used before live ≤ FrameSums.used after next)
    (cap : FrameSums.used after next ≤ limit) (sameDepth : next.length = live.length) :
    value limit after next false < value limit before live true := by
  cases live with
  | nil => exact (nonempty rfl).elim
  | cons head rest =>
    cases next with
    | nil => simp at sameDepth
    | cons nextHead nextRest =>
      simp only [value, phasePrice, List.length_cons]
      simp only [List.length_cons] at sameDepth
      omega

theorem child_exit (limit : Nat) (before after : Memory) (live next : List (BitVec 64)) (nextActive : Bool)
    (monotone : FrameSums.used before live ≤ FrameSums.used after next)
    (cap : FrameSums.used after next ≤ limit) (removed : next.length + 1 = live.length) :
    value limit after next nextActive < value limit before live false := by
  cases live with
  | nil => simp at removed
  | cons head rest =>
    cases next with
    | nil => simp only [value, phasePrice, List.length_cons]; omega
    | cons nextHead nextRest =>
      cases nextActive <;> simp only [value, phasePrice, List.length_cons]
      all_goals simp only [List.length_cons] at removed
      all_goals omega

theorem root_exit (limit : Nat) (before after : Memory) (live : List (BitVec 64)) (active : Bool)
    (nonempty : live ≠ []) : value limit after [] false < value limit before live active := by
  cases live with
  | nil => exact (nonempty rfl).elim
  | cons head rest => cases active <;> simp only [value, phasePrice, List.length_cons] <;> omega

theorem initial (memory : Memory) (root gas : BitVec 64) (active : Bool) (seed : GasSeed memory root gas) :
    value gas.toNat memory [root] active ≤ 3 * gas.toNat + 3 := by
  cases active <;> simp [value, phasePrice, FrameSums.used, wordAt, seed.used, WitnessRadix.MemoryBytes.wordBits] <;> omega

/-- Conditional initial rank ceiling, not an instantiated iteration theorem
or a source/target runtime bound. -/
theorem initial_capped (memory : Memory) (root gas : BitVec 64) (active : Bool)
    (seed : GasSeed memory root gas) (cap : gas.toNat ≤ 16777216) :
    value gas.toNat memory [root] active ≤ 50331651 := by
  have bounded := initial memory root gas active seed
  omega

end InitECandidate.Solver.GasBudget.FrameRank

#print axioms InitECandidate.Solver.GasBudget.FrameRank.charged
#print axioms InitECandidate.Solver.GasBudget.FrameRank.terminal
#print axioms InitECandidate.Solver.GasBudget.FrameRank.child_exit
#print axioms InitECandidate.Solver.GasBudget.FrameRank.root_exit
#print axioms InitECandidate.Solver.GasBudget.FrameRank.initial_capped
