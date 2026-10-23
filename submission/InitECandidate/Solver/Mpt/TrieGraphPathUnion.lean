import InitECandidate.Solver.Mpt.TrieGraphUnion
import InitECandidate.Solver.Mpt.TriePathBytesSeparation
import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.PathBytes.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (be : Bool) (left : first.PathBytes be) (right : second.PathBytes be) :
    (first.union second).PathBytes be := by
  constructor
  · intro node member active tag
    rcases member with old|fresh
    · exact left.span node old active tag
    · exact right.span node fresh active tag
  · intro node member active tag
    rcases member with old|fresh
    · exact left.positive node old active tag
    · exact right.positive node fresh active tag

theorem Graph.PathRegions.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (lower middle upper : Nat)
    (left : first.PathRegions lower middle) (right : second.PathRegions middle upper)
    (ordered : lower≤middle) (grows : middle≤upper) : (first.union second).PathRegions lower upper := by
  intro node member active tag
  rcases member with old|fresh
  · exact left.weaken first lower middle lower upper (Nat.le_refl _) grows node old active tag
  · exact right.weaken second middle upper lower upper ordered (Nat.le_refl _) node fresh active tag

/-- Both cross-allocation path/node pairs are separated by the real
aligned heap frontier. Path pointers may themselves be unaligned and path
buffers may still be shared or sliced within either component graph. -/
theorem Graph.PathSeparated.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (be : Bool) (nodeLower pathLower middle upper : Nat)
    (leftNodes : first.Regions nodeLower middle) (rightNodes : second.Regions middle upper)
    (leftPaths : first.PathRegions pathLower middle) (rightPaths : second.PathRegions middle upper)
    (leftBytes : first.PathBytes be) (rightBytes : second.PathBytes be)
    (left : first.PathSeparated) (right : second.PathSeparated) (aligned : middle%8=0) : (first.union second).PathSeparated := by
  intro current member active tag index inside owner ownerMember ownerActive offset offsetInside
  rcases member with old|fresh
  · rcases ownerMember with ownerOld|ownerFresh
    · exact left current old active tag index inside owner ownerOld ownerActive offset offsetInside
    · have span:=leftBytes.span current old active tag
      have before:=(leftPaths current old active tag).2
      obtain ⟨floor,arena,ownerAligned,upper⟩:=rightNodes owner ownerFresh ownerActive
      exact span.apart_before memory domain be _ owner _ _ arena (before.trans floor) index inside offset offsetInside
  · rcases ownerMember with ownerOld|ownerFresh
    · have span:=rightBytes.span current fresh active tag
      have after:=(rightPaths current fresh active tag).1
      obtain ⟨floor,arena,ownerAligned,before⟩:=leftNodes owner ownerOld ownerActive
      intro same
      have number:=byteAddress_toNat (wordAt memory (current+32#64)) index (by have fits:=span.fits; omega)
      have ownerNumber:=byteAddress_toNat owner offset (by have upper:=arena.upper; omega)
      have numeric:=congrArg BitVec.toNat same
      rw [AllocatedBytes.aligned_number,number,ownerNumber] at numeric
      omega
    · exact right current fresh active tag index inside owner ownerFresh ownerActive offset offsetInside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBytes.union
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.union
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathSeparated.union
