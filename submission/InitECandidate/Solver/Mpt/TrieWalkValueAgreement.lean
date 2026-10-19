import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.Mpt.TrieWalkGraphHash

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix

variable {property : BitVec 64 → BitVec 64 → Prop}

inductive ValueFootprint {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) : BitVec 64 → Prop where
  | leafPointer (node) (member : graph.valid node) (active : node≠0#64) (tag : wordAt memory node=1#64) : ValueFootprint graph (node+48#64)
  | leafLength (node) (member : graph.valid node) (active : node≠0#64) (tag : wordAt memory node=1#64) : ValueFootprint graph (node+56#64)
  | branchPointer (node) (member : graph.valid node) (active : node≠0#64) (notHash : wordAt memory node≠0#64)
      (notLeaf : wordAt memory node≠1#64) (notExtension : wordAt memory node≠2#64) : ValueFootprint graph (node+160#64)
  | branchLength (node) (member : graph.valid node) (active : node≠0#64) (notHash : wordAt memory node≠0#64)
      (notLeaf : wordAt memory node≠1#64) (notExtension : wordAt memory node≠2#64) : ValueFootprint graph (node+168#64)

def ValueView.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (node pointerOffset lengthOffset : BitVec 64) (limit : Nat)
    (view : ValueView memory domain node pointerOffset lengthOffset limit property)
    (sameDomain : domain'=domain)
    (pointer : memory' (node+pointerOffset)=memory (node+pointerOffset))
    (length : memory' (node+lengthOffset)=memory (node+lengthOffset)) :
    ValueView memory' domain' node pointerOffset lengthOffset limit property := {
  pointer := view.pointer
  length := view.length
  pointerMapped := by rw [sameDomain]; exact view.pointerMapped
  pointerStored := pointer.trans view.pointerStored
  lengthMapped := by rw [sameDomain]; exact view.lengthMapped
  lengthStored := length.trans view.lengthStored
  payload := by rw [sameDomain]; exact view.payload
  extra := view.extra }

/-- Preserve actual value fields through a structural graph reconstruction.
The mapped payload contents remain unrestricted. -/
def Values.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (valueLimit : Nat) (values : Values graph valueLimit property)
    (validEq : next.valid=graph.valid) (sameDomain : domain'=domain)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node)
    (agree : ∀ query,ValueFootprint graph query → memory' query=memory query) : Values next valueLimit property := by
  constructor
  · intro node member active tag
    have oldMember : graph.valid node := by rwa [validEq] at member
    have oldTag : wordAt memory node=1#64 := by rwa [tags node oldMember active] at tag
    exact ValueView.of_agreement memory memory' domain domain' node 48#64 56#64 valueLimit
      (values.leaf node oldMember active oldTag) sameDomain
      (agree _ (.leafPointer node oldMember active oldTag)) (agree _ (.leafLength node oldMember active oldTag))
  · intro node member active notHash notLeaf notExtension
    have oldMember : graph.valid node := by rwa [validEq] at member
    rw [tags node oldMember active] at notHash notLeaf notExtension
    exact ValueView.of_agreement memory memory' domain domain' node 160#64 168#64 valueLimit
      (values.branch node oldMember active notHash notLeaf notExtension) sameDomain
      (agree _ (.branchPointer node oldMember active notHash notLeaf notExtension))
      (agree _ (.branchLength node oldMember active notHash notLeaf notExtension))

def ValueProtected {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (out : BitVec 64) : Prop :=
  ∀ query,ValueFootprint graph query → ∀ offset<64,query≠panByteAlignHOL (width := 64) (byteAddress out offset)

theorem Values.after_output (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property) (out : BitVec 64)
    (protectedGraph : graph.Protected out) (protectedValues : ValueProtected graph out)
    (frame : KeyToNibbles.OutputFrame source post out) :
    ∃ nextGraph : Graph post.memory post.memaddrs,nextGraph.valid=graph.valid ∧ Nonempty (Values nextGraph valueLimit property) := by
  obtain ⟨next,validEq⟩ := Graph.after_output source post graph out protectedGraph frame
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs frame.fields
  change post.memaddrs=source.memaddrs at domainEq
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node := by
    intro node member active
    unfold wordAt
    rw [frame.memory node (protectedGraph node (.header node member active))]
  exact ⟨next,validEq,⟨Values.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next valueLimit values validEq domainEq tags
    (fun query required => frame.memory query (protectedValues query required))⟩⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.after_output
