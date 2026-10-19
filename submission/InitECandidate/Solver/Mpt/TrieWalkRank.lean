import InitECandidate.Solver.Mpt.TrieWalkBranch

namespace InitECandidate.Solver.Mpt.TrieWalk.Rank
open Flapjack PanSemStateFiniteExact GasBudget

/-- An extension can consume zero nibbles. Its phase pays for that hop when
the actual next node is not another extension. Reachability remains separate. -/
def phase (memory : Memory) (node : BitVec 64) : Nat := if wordAt memory node = 2#64 then 1 else 0
def value (limit : Nat) (memory : Memory) (node position : BitVec 64) : Nat :=
  if node = 0#64 then 0 else 2 * (limit - position.toNat) + phase memory node + 1

theorem phase_le (memory : Memory) (node : BitVec 64) : phase memory node ≤ 1 := by
  unfold phase
  split <;> decide

theorem positive (limit : Nat) (memory : Memory) (node position : BitVec 64) (active : node ≠ 0#64) :
    0 < value limit memory node position := by
  simp only [value, if_neg active]
  omega

theorem upper (limit : Nat) (memory : Memory) (node position : BitVec 64) :
    value limit memory node position ≤ 2 * limit + 2 := by
  have bound := phase_le memory node
  unfold value
  split <;> omega

theorem advances (limit : Nat) (before after : Memory) (node nextNode position nextPosition : BitVec 64)
    (active : node ≠ 0#64) (progress : position.toNat < nextPosition.toNat) (bounded : nextPosition.toNat ≤ limit) :
    value limit after nextNode nextPosition < value limit before node position := by
  have bound := phase_le after nextNode
  have funded := positive limit before node position active
  unfold value
  rw [if_neg active]
  split <;> omega

theorem zero_extension (limit : Nat) (before after : Memory) (node nextNode position : BitVec 64)
    (active : node ≠ 0#64) (extension : wordAt before node = 2#64)
    (next : nextNode = 0#64 ∨ wordAt after nextNode ≠ 2#64) :
    value limit after nextNode position < value limit before node position := by
  rcases next with stopped | other
  · simp only [value, if_pos stopped, if_neg active]
    omega
  · by_cases stopped : nextNode = 0#64
    · simp only [value, if_pos stopped, if_neg active]
      omega
    · simp only [value, if_neg stopped, if_neg active, phase, if_pos extension, if_neg other]
      omega

/-- This instantiates the numeric step for the actual checked branch run.
It does not establish the full trie-loop invariant or its initial reachability. -/
theorem branch_decreases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nextNode position : BitVec 64) (limit : Nat) (active : node ≠ 0#64)
    (small : limit ≤ 64) (bounded : position.toNat ≤ limit)
    (posCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (run : evaluateHOLFiniteState source branch = (none, post)) :
    value limit post.memory nextNode (position + 1#64) < value limit source.memory node position := by
  obtain ⟨inside, advanced, number, fields⟩ := branch_normal source post position limit small bounded posCell limitCell run
  apply advances limit source.memory post.memory node nextNode position (position + 1#64) active
  · rw [number]
    omega
  · rw [number]
    omega

end InitECandidate.Solver.Mpt.TrieWalk.Rank

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.phase_le
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.positive
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.upper
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.advances
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.zero_extension
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Rank.branch_decreases
