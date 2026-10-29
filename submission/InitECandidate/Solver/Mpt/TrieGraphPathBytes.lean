import InitECandidate.Solver.Mpt.TriePathBytes
import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Actual full path bytes for registered leaves and extensions. The real
decoder and mutation constructors also retain positive extension lengths. -/
structure Graph.PathBytes {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (be : Bool) : Prop where
  span : ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
    NibbleSpan memory domain be (wordAt memory (node+32#64)) (wordAt memory (node+40#64)).toNat
  positive : ∀ node,graph.valid node → node≠0#64 → wordAt memory node=2#64 → 0<(wordAt memory (node+40#64)).toNat

def Graph.PathRegions {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (lower upper : Nat) : Prop:=
  ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
    lower≤(wordAt memory (node+32#64)).toNat ∧ (wordAt memory (node+32#64)).toNat+(wordAt memory (node+40#64)).toNat≤upper

/-- Path buffers may be shared or sliced, but their backing words must
remain separate from every registered node allocation's mutable fields. -/
def Graph.PathSeparated {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) : Prop:=
  ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
    ∀ index<(wordAt memory (node+40#64)).toNat,∀ owner,graph.valid owner → owner≠0#64 →
      ∀ offset<nodeBytes (wordAt memory owner),
        panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index)≠byteAddress owner offset

theorem Graph.path_word_agreement {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain)
    (memory' : Memory) (agree : ∀ query,graph.Footprint query → memory' query=memory query)
    (node : BitVec 64) (member : graph.valid node) (active : node≠0#64) (tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64) :
    wordAt memory' (node+32#64)=wordAt memory (node+32#64) ∧ wordAt memory' (node+40#64)=wordAt memory (node+40#64) := by
  constructor
  · unfold wordAt
    rw [agree _ (.pointer node member active tag)]
  · unfold wordAt
    rw [agree _ (.size node member active tag)]

theorem Graph.PathBytes.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop) (be be' : Bool)
    (graph : Graph memory domain) (next : Graph memory' domain') (paths : graph.PathBytes be)
    (validEq : next.valid=graph.valid) (sameDomain : domain'=domain) (sameEndian : be'=be)
    (agree : ∀ query,graph.Footprint query → memory' query=memory query)
    (bytes : ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      ∀ index<(wordAt memory (node+40#64)).toNat,
        memory' (panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index))=
        memory (panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index))) : next.PathBytes be' := by
  have tags (node : BitVec 64) (member : graph.valid node) (active : node≠0#64) : wordAt memory' node=wordAt memory node:=by
    unfold wordAt
    rw [agree node (.header node member active)]
  constructor
  · intro node member active tag
    have oldMember : graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [tags node oldMember active] at tag
    have fields:=graph.path_word_agreement memory' agree node oldMember active oldTag
    rw [fields.1,fields.2]
    exact (paths.span node oldMember active oldTag).of_agreement memory memory' domain domain' be be' _ _ sameDomain sameEndian (bytes node oldMember active oldTag)
  · intro node member active tag
    have oldMember : graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt memory node=2#64:=by rwa [tags node oldMember active] at tag
    rw [(graph.path_word_agreement memory' agree node oldMember active (Or.inr oldTag)).2]
    exact paths.positive node oldMember active oldTag

theorem Graph.PathRegions.weaken {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain)
    (lower upper smaller larger : Nat) (regions : graph.PathRegions lower upper) (first : smaller≤lower) (last : upper≤larger) :
    graph.PathRegions smaller larger := by
  intro node member active tag
  obtain ⟨floor,before⟩:=regions node member active tag
  exact ⟨Nat.le_trans first floor,Nat.le_trans before last⟩

theorem Graph.PathRegions.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (lower upper : Nat) (regions : graph.PathRegions lower upper)
    (validEq : next.valid=graph.valid) (agree : ∀ query,graph.Footprint query → memory' query=memory query) : next.PathRegions lower upper := by
  intro node member active tag
  have oldMember : graph.valid node:=by rwa [validEq] at member
  have tagEq : wordAt memory' node=wordAt memory node:=by unfold wordAt; rw [agree node (.header node oldMember active)]
  have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [tagEq] at tag
  have fields:=graph.path_word_agreement memory' agree node oldMember active oldTag
  rw [fields.1,fields.2]
  exact regions node oldMember active oldTag

theorem Graph.PathSeparated.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (separated : graph.PathSeparated)
    (validEq : next.valid=graph.valid) (agree : ∀ query,graph.Footprint query → memory' query=memory query) : next.PathSeparated := by
  intro node member active tag index inside owner ownerMember ownerActive offset offsetInside
  have oldMember : graph.valid node:=by rwa [validEq] at member
  have oldOwner : graph.valid owner:=by rwa [validEq] at ownerMember
  have tagEq : wordAt memory' node=wordAt memory node:=by unfold wordAt; rw [agree node (.header node oldMember active)]
  have ownerTagEq : wordAt memory' owner=wordAt memory owner:=by unfold wordAt; rw [agree owner (.header owner oldOwner ownerActive)]
  have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [tagEq] at tag
  have fields:=graph.path_word_agreement memory' agree node oldMember active oldTag
  rw [fields.2] at inside
  rw [ownerTagEq] at offsetInside
  rw [fields.1]
  exact separated node oldMember active oldTag index inside owner oldOwner ownerActive offset offsetInside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.path_word_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBytes.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.weaken
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathRegions.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathSeparated.of_agreement
