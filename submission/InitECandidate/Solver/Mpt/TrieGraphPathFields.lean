import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Path ownership depends on tags and path fields. Child pointers and
values may change while these actual path fields remain unchanged. -/
structure Graph.PathFields {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (memory' : Memory) : Prop where
  tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node
  fields : ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
    wordAt memory' (node+32#64)=wordAt memory (node+32#64) ∧ wordAt memory' (node+40#64)=wordAt memory (node+40#64)

theorem Graph.PathBytes.of_fields (memory memory' : Memory) (domain domain' : BitVec 64 → Prop) (be be' : Bool)
    (graph : Graph memory domain) (next : Graph memory' domain') (paths : graph.PathBytes be)
    (validEq : next.valid=graph.valid) (sameDomain : domain'=domain) (sameEndian : be'=be) (fields : graph.PathFields memory')
    (bytes : ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      ∀ index<(wordAt memory (node+40#64)).toNat,
        memory' (panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index))=
        memory (panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index))) : next.PathBytes be' := by
  constructor
  · intro node member active tag
    have oldMember : graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [fields.tags node oldMember active] at tag
    have words:=fields.fields node oldMember active oldTag
    rw [words.1,words.2]
    exact (paths.span node oldMember active oldTag).of_agreement memory memory' domain domain' be be' _ _ sameDomain sameEndian (bytes node oldMember active oldTag)
  · intro node member active tag
    have oldMember : graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt memory node=2#64:=by rwa [fields.tags node oldMember active] at tag
    rw [(fields.fields node oldMember active (Or.inr oldTag)).2]
    exact paths.positive node oldMember active oldTag

theorem Graph.PathRegions.of_fields (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (lower upper : Nat) (regions : graph.PathRegions lower upper)
    (validEq : next.valid=graph.valid) (fields : graph.PathFields memory') : next.PathRegions lower upper := by
  intro node member active tag
  have oldMember : graph.valid node:=by rwa [validEq] at member
  have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [fields.tags node oldMember active] at tag
  have words:=fields.fields node oldMember active oldTag
  rw [words.1,words.2]
  exact regions node oldMember active oldTag

theorem Graph.PathSeparated.of_fields (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (separated : graph.PathSeparated)
    (validEq : next.valid=graph.valid) (fields : graph.PathFields memory') : next.PathSeparated := by
  intro node member active tag index inside owner ownerMember ownerActive offset offsetInside
  have oldMember : graph.valid node:=by rwa [validEq] at member
  have oldOwner : graph.valid owner:=by rwa [validEq] at ownerMember
  have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [fields.tags node oldMember active] at tag
  have words:=fields.fields node oldMember active oldTag
  rw [words.2] at inside
  rw [fields.tags owner oldOwner ownerActive] at offsetInside
  rw [words.1]
  exact separated node oldMember active oldTag index inside owner oldOwner ownerActive offset offsetInside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBytes.of_fields
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.of_fields
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathSeparated.of_fields
