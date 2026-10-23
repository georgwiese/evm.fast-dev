import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.PathBytes.empty (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) : (Graph.empty memory domain).PathBytes be := by
  constructor
  all_goals intro node member active; exact (active member).elim

theorem Graph.PathRegions.empty (memory : Memory) (domain : BitVec 64 → Prop) (lower upper : Nat) : (Graph.empty memory domain).PathRegions lower upper := by
  intro node member active
  exact (active member).elim

theorem Graph.PathSeparated.empty (memory : Memory) (domain : BitVec 64 → Prop) : (Graph.empty memory domain).PathSeparated := by
  intro node member active
  exact (active member).elim

/-- Register byte facts from a node's actual initialized path fields. The
old byte registry already lives at this same current memory. -/
theorem Graph.PathBytes.register {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (paths : graph.PathBytes be) (node : BitVec 64) (data : Registration graph node)
    (span : (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      NibbleSpan memory domain be (wordAt memory (node+32#64)) (wordAt memory (node+40#64)).toNat)
    (positive : wordAt memory node=2#64 → 0<(wordAt memory (node+40#64)).toNat) : (graph.register node data).PathBytes be := by
  constructor
  · intro current member active tag
    rcases member with old|fresh
    · exact paths.span current old active tag
    · subst current; exact span tag
  · intro current member active tag
    rcases member with old|fresh
    · exact paths.positive current old active tag
    · subst current; exact positive tag

theorem Graph.PathRegions.register {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.PathRegions lower upper) (node : BitVec 64) (data : Registration graph node)
    (bounds : (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      lower≤(wordAt memory (node+32#64)).toNat ∧ (wordAt memory (node+32#64)).toNat+(wordAt memory (node+40#64)).toNat≤upper) :
    (graph.register node data).PathRegions lower upper := by
  intro current member active tag
  rcases member with old|fresh
  · exact regions current old active tag
  · subst current; exact bounds tag

/-- New registration preserves separation using current allocation facts
for the two new combinations: older paths/new node and new path/all nodes.
Buffers may be shared; no input-tree acyclicity premise is involved. -/
theorem Graph.PathSeparated.register {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (separated : graph.PathSeparated) (node : BitVec 64) (data : Registration graph node)
    (oldApart : ∀ current,graph.valid current → current≠0#64 → (wordAt memory current=1#64 ∨ wordAt memory current=2#64) →
      ∀ index<(wordAt memory (current+40#64)).toNat,node≠0#64 → ∀ offset<nodeBytes (wordAt memory node),
        panByteAlignHOL (width:=64) (byteAddress (wordAt memory (current+32#64)) index)≠byteAddress node offset)
    (newApart : (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      ∀ index<(wordAt memory (node+40#64)).toNat,∀ owner,graph.valid owner ∨ owner=node → owner≠0#64 →
        ∀ offset<nodeBytes (wordAt memory owner),
          panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index)≠byteAddress owner offset) :
    (graph.register node data).PathSeparated := by
  intro current member active tag index inside owner ownerMember ownerActive offset offsetInside
  rcases member with old|fresh
  · rcases ownerMember with ownerOld|ownerFresh
    · exact separated current old active tag index inside owner ownerOld ownerActive offset offsetInside
    · subst owner
      exact oldApart current old active tag index inside ownerActive offset offsetInside
  · subst current
    exact newApart tag index inside owner ownerMember ownerActive offset offsetInside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBytes.empty
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.empty
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathSeparated.empty
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBytes.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathSeparated.register
