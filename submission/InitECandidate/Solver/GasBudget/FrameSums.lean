import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.FrameSums
open Flapjack

/-- Physical regular budget and used-word sums over the current live frame
list. Reachability/ownership of that list is a separate global obligation. -/
def budget (memory : Memory) (frames : List (BitVec 64)) : Nat :=
  (frames.map (regularBudget memory)).sum
def used (memory : Memory) (frames : List (BitVec 64)) : Nat :=
  (frames.map (fun frame => (wordAt memory (frame + 184#64)).toNat)).sum

theorem used_le_budget (memory : Memory) (frames : List (BitVec 64)) : used memory frames ≤ budget memory frames := by
  induction frames with
  | nil => simp [used, budget]
  | cons frame frames ih =>
    have head : (wordAt memory (frame + 184#64)).toNat ≤ regularBudget memory frame := by unfold regularBudget; omega
    simpa only [used, budget, List.map_cons, List.sum_cons] using Nat.add_le_add head ih

theorem budget_congr (before after : Memory) (frames : List (BitVec 64))
    (same : ∀ frame ∈ frames, ∀ offset ∈ ([64, 184, 192] : List Nat),
      after (frame + BitVec.ofNat 64 offset) = before (frame + BitVec.ofNat 64 offset)) : budget after frames = budget before frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    have head : regularBudget after frame = regularBudget before frame := by
      simp only [regularBudget, wordAt, same frame (by simp) 64 (by simp), same frame (by simp) 184 (by simp), same frame (by simp) 192 (by simp)]
    have tail := ih (by intro other member; exact same other (List.mem_cons_of_mem _ member))
    change regularBudget after frame + budget after frames = regularBudget before frame + budget before frames
    rw [head, tail]

theorem used_congr (before after : Memory) (frames : List (BitVec 64))
    (same : ∀ frame ∈ frames, after (frame + 184#64) = before (frame + 184#64)) : used after frames = used before frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    have tail := ih (by intro other member; exact same other (List.mem_cons_of_mem _ member))
    change (wordAt after (frame + 184#64)).toNat + used after frames = (wordAt before (frame + 184#64)).toNat + used before frames
    rw [tail]
    simp only [wordAt, same frame (by simp)]

def Outside (parent : BitVec 64) (ancestors : List (BitVec 64)) : Prop :=
  ∀ frame ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
    frame + BitVec.ofNat 64 offset ≠ parent + 64#64 ∧ frame + BitVec.ofNat 64 offset ≠ parent + 184#64

theorem outside_preserved (before after : Memory) (parent : BitVec 64) (ancestors : List (BitVec 64))
    (apart : Outside parent ancestors)
    (footprint : ∀ address, address ≠ parent + 64#64 → address ≠ parent + 184#64 → after address = before address) :
    budget after ancestors = budget before ancestors ∧ used after ancestors = used before ancestors := by
  have same : ∀ frame ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      after (frame + BitVec.ofNat 64 offset) = before (frame + BitVec.ofNat 64 offset) := by
    intro frame member offset inside
    exact footprint _ (apart frame member offset inside).1 (apart frame member offset inside).2
  exact ⟨budget_congr before after ancestors same, used_congr before after ancestors (by intro frame member; exact same frame member 184 (by simp))⟩

/-- Opening a genuinely fresh child transfers its budget seed into the live
sum and adds no used credit when its actual used word is zero. -/
theorem add_child (memory : Memory) (frames : List (BitVec 64)) (child : BitVec 64) (seed : Nat)
    (childBudget : regularBudget memory child = seed) (childUsed : memory (child + 184#64) = .word 0#64) :
    budget memory (child :: frames) = seed + budget memory frames ∧ used memory (child :: frames) = used memory frames := by
  constructor
  · change regularBudget memory child + budget memory frames = seed + budget memory frames
    rw [childBudget]
  · change (wordAt memory (child + 184#64)).toNat + used memory frames = used memory frames
    simp [wordAt, childUsed, WitnessRadix.MemoryBytes.wordBits]

end InitECandidate.Solver.GasBudget.FrameSums

#print axioms InitECandidate.Solver.GasBudget.FrameSums.used_le_budget
#print axioms InitECandidate.Solver.GasBudget.FrameSums.outside_preserved
#print axioms InitECandidate.Solver.GasBudget.FrameSums.add_child
