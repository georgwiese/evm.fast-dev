import InitECandidate.Solver.Mpt.TrieProtectedWord
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A caller word avoids every backing word of the complete borrowed
path. Length is not truncated to the64-nibble query bound. -/
def PathWordAway (pointer : BitVec 64) (length : Nat) (query : BitVec 64) : Prop :=
  ∀ index<length,query≠panByteAlignHOL (width:=64) (byteAddress pointer index)

theorem PathWordAway.before (pointer query : BitVec 64) (length : Nat)
    (fits : pointer.toNat+length<2^64) (before : query.toNat+8≤pointer.toNat) : PathWordAway pointer length query := by
  intro index inside equal
  have number:=byteAddress_toNat pointer index (by omega)
  have same:=congrArg BitVec.toNat equal
  rw [AllocatedBytes.aligned_number,number] at same
  omega

/-- Any actual window inherits the full backing-word avoidance, even
when its pointer is an unaligned slice of an older stored path. -/
theorem PathWordAway.window (pointer position query : BitVec 64) (length count : Nat)
    (away : PathWordAway pointer length query) (before : position.toNat≤length) (within : count≤length-position.toNat) :
    PathWordAway (pointer+position) count query := by
  intro index inside
  have shifted : byteAddress (pointer+position) index=byteAddress pointer (position.toNat+index):=by
    simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  rw [shifted]
  exact away _ (by omega)

theorem Graph.ProtectedWord.stored {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query node : BitVec 64) (safe : graph.ProtectedWord query)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64) :
    PathWordAway (wordAt memory (node+32#64)) (wordAt memory (node+40#64)).toNat query :=
  safe.paths node member active tag

/-- Extend protection through one actual fresh registration. Old node
descriptors survive by their true field frame; the new node lies above
the caller word, and its actual stored path supplies the remaining case. -/
theorem Graph.ProtectedWord.after_fresh {memory memory' : Memory} {domain domain' : BitVec 64→Prop}
    (graph : Graph memory domain) (next : Graph memory' domain') (query fresh : BitVec 64)
    (safe : graph.ProtectedWord query) (fields : graph.PathFields memory')
    (members : ∀ node,next.valid node ↔ graph.valid node ∨ node=fresh)
    (before : query.toNat<fresh.toNat) (arena : AllocatedBytes.Arena fresh (nodeBytes (wordAt memory' fresh)))
    (newPaths : (wordAt memory' fresh=1#64 ∨ wordAt memory' fresh=2#64) →
      PathWordAway (wordAt memory' (fresh+32#64)) (wordAt memory' (fresh+40#64)).toNat query) : next.ProtectedWord query := by
  constructor
  · intro node member active offset inside equal
    rcases (members node).mp member with old|new
    · rw [fields.tags node old active] at inside
      exact safe.nodes node old active offset inside equal
    · subst node
      have number:=byteAddress_toNat fresh offset (by have upper:=arena.upper; omega)
      have same:=congrArg BitVec.toNat equal
      rw [number] at same
      omega
  · intro node member active tag index inside
    rcases (members node).mp member with old|new
    · have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [fields.tags node old active] at tag
      have saved:=fields.fields node old active oldTag
      rw [saved.2] at inside
      rw [saved.1]
      exact safe.paths node old active oldTag index inside
    · subst node
      exact newPaths tag index inside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.PathWordAway.before
#print axioms InitECandidate.Solver.Mpt.TrieWalk.PathWordAway.window
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.stored
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.after_fresh
