import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.TriePathBytesRegister

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A fresh leaf or positive extension borrows a protected current
buffer. The registered node cannot overwrite any old or borrowed path. -/
theorem Graph.register_borrowed_paths {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (lower upper nextUpper : Nat)
    (paths : graph.PathBytes be) (regions : graph.PathRegions lower upper) (separated : graph.PathSeparated)
    (node pointer length : BitVec 64) (data : Registration graph node)
    (_tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64)
    (pointerStored : wordAt memory (node+32#64)=pointer) (lengthStored : wordAt memory (node+40#64)=length)
    (positive : wordAt memory node=2#64 → 0<length.toNat)
    (arena : AllocatedBytes.Arena node (nodeBytes (wordAt memory node)))
    (fresh : upper≤node.toNat) (grows : upper≤nextUpper)
    (buffer : graph.PathBuffer be lower upper pointer length.toNat) :
    (graph.register node data).PathBytes be ∧ (graph.register node data).PathRegions lower nextUpper ∧
      (graph.register node data).PathSeparated := by
  have newSpan : NibbleSpan memory domain be (wordAt memory (node+32#64)) (wordAt memory (node+40#64)).toNat:=by
    rw [pointerStored,lengthStored]
    exact buffer.span
  refine ⟨paths.register graph be node data (fun _=>newSpan) ?_,?_,?_⟩
  · intro extensionTag
    rw [lengthStored]
    exact positive extensionTag
  · apply Graph.PathRegions.register graph lower nextUpper (regions.weaken graph lower upper lower nextUpper (Nat.le_refl _) grows) node data
    intro pathTag
    rw [pointerStored,lengthStored]
    exact ⟨buffer.bounds.1,buffer.bounds.2.trans grows⟩
  · apply separated.register graph node data
    · intro current member active pathTag index inside nodeActive offset within
      exact (paths.span current member active pathTag).apart_before memory domain be _ node _ _ arena
        ((regions current member active pathTag).2.trans fresh) index inside offset within
    · intro pathTag index inside owner ownerMember ownerActive offset within
      rw [lengthStored] at inside
      rw [pointerStored]
      rcases ownerMember with old|new
      · exact buffer.apart index inside owner old ownerActive offset within
      · subst owner
        exact buffer.span.apart_before memory domain be pointer node length.toNat _ arena (buffer.bounds.2.trans fresh) index inside offset within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.register_borrowed_paths
