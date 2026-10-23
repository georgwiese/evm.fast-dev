import InitECandidate.Solver.Mpt.TrieWalkMemory
import InitECandidate.Solver.Mpt.KeyToNibblesFootprint

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix

/-- Structural words needed by the walk's physical graph invariant.
Path byte contents affect the actual result but need only stay mapped for
the runtime proof. -/
inductive Graph.Footprint {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) : BitVec 64 → Prop where
  | header (node) (member : graph.valid node) (active : node ≠ 0#64) : graph.Footprint node
  | pointer (node) (member : graph.valid node) (active : node ≠ 0#64)
      (tag : wordAt memory node = 1#64 ∨ wordAt memory node = 2#64) : graph.Footprint (node + 32#64)
  | size (node) (member : graph.valid node) (active : node ≠ 0#64)
      (tag : wordAt memory node = 1#64 ∨ wordAt memory node = 2#64) : graph.Footprint (node + 40#64)
  | extension (node) (member : graph.valid node) (active : node ≠ 0#64)
      (tag : wordAt memory node = 2#64) : graph.Footprint (node + 48#64)
  | branch (node) (member : graph.valid node) (active : node ≠ 0#64)
      (notHash : wordAt memory node ≠ 0#64) (notLeaf : wordAt memory node ≠ 1#64) (notExtension : wordAt memory node ≠ 2#64)
      (index : Nat) (inside : index < 16) : graph.Footprint (node + 32#64 + BitVec.ofNat 64 (index * 8))

def Graph.Protected {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (out : BitVec 64) : Prop :=
  ∀ query, graph.Footprint query → ∀ offset < 64, query ≠ panByteAlignHOL (width := 64) (byteAddress out offset)

/-- Preserve a current closed graph under agreement on exactly its
structural words and the memory domain. No new graph is a premise. -/
def Graph.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop) (graph : Graph memory domain)
    (sameDomain : domain' = domain)
    (agree : ∀ query, graph.Footprint query → memory' query = memory query) : Graph memory' domain' := by
  have tagEq : ∀ node, graph.valid node → node ≠ 0#64 → wordAt memory' node = wordAt memory node := by
    intro node member active
    unfold wordAt
    rw [agree node (.header node member active)]
  refine {
    valid := graph.valid
    null := graph.null
    header := ?_
    path := ?_
    extension := ?_
    zeroHop := ?_
    branch := ?_
    kindBound := by
      intro node member active
      rw [tagEq node member active]
      exact graph.kindBound node member active }
  · intro node member active
    obtain ⟨mapped, stored⟩ := graph.header node member active
    exact ⟨by rwa [sameDomain], by rw [agree node (.header node member active), tagEq node member active]; exact stored⟩
  · intro node member active tag
    have oldTag : wordAt memory node = 1#64 ∨ wordAt memory node = 2#64 := by rwa [tagEq node member active] at tag
    let old := graph.path node member active oldTag
    exact {
      size := old.size, pointer := old.pointer
      sizeMapped := by rw [sameDomain]; exact old.sizeMapped
      sizeStored := by rw [agree _ (.size node member active oldTag)]; exact old.sizeStored
      pointerMapped := by rw [sameDomain]; exact old.pointerMapped
      pointerStored := by rw [agree _ (.pointer node member active oldTag)]; exact old.pointerStored
      fits := old.fits
      mapped := by rw [sameDomain]; exact old.mapped }
  · intro node member active tag
    have oldTag : wordAt memory node = 2#64 := by rwa [tagEq node member active] at tag
    let old := graph.extension node member active oldTag
    exact {
      child := old.child
      mapped := by rw [sameDomain]; exact old.mapped
      stored := by rw [agree _ (.extension node member active oldTag)]; exact old.stored
      member := old.member }
  · intro node member active tag zero
    have oldTag : wordAt memory node = 2#64 := by rwa [tagEq node member active] at tag
    have sizeEq : wordAt memory' (node + 40#64) = wordAt memory (node + 40#64) := by
      unfold wordAt
      rw [agree _ (.size node member active (Or.inr oldTag))]
    have oldZero : wordAt memory (node + 40#64) = 0#64 := sizeEq.symm.trans zero
    have next := graph.zeroHop node member active oldTag oldZero
    let old := graph.extension node member active oldTag
    change old.child = 0#64 ∨ wordAt memory' old.child ≠ 2#64
    rcases next with stopped | other
    · exact Or.inl stopped
    · by_cases stopped : old.child = 0#64
      · exact Or.inl stopped
      · right
        rw [tagEq old.child old.member stopped]
        exact other
  · intro node member active notHash notLeaf notExtension index inside
    have eq := tagEq node member active
    rw [eq] at notHash notLeaf notExtension
    let old := graph.branch node member active notHash notLeaf notExtension index inside
    exact {
      child := old.child
      mapped := by rw [sameDomain]; exact old.mapped
      stored := by rw [agree _ (.branch node member active notHash notLeaf notExtension index inside)]; exact old.stored
      member := old.member }

theorem Graph.of_agreement_valid (memory memory' : Memory) (domain domain' : BitVec 64 → Prop) (graph : Graph memory domain)
    (sameDomain : domain' = domain) (agree : ∀ query, graph.Footprint query → memory' query = memory query) :
    (Graph.of_agreement memory memory' domain domain' graph sameDomain agree).valid = graph.valid := rfl

theorem Graph.after_output (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (out : BitVec 64) (protectedGraph : graph.Protected out)
    (frame : KeyToNibbles.OutputFrame source post out) :
    ∃ nextGraph : Graph post.memory post.memaddrs, nextGraph.valid = graph.valid := by
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs frame.fields
  change post.memaddrs = source.memaddrs at domainEq
  have agree : ∀ query, graph.Footprint query → post.memory query = source.memory query := by
    intro query required
    exact frame.memory query (protectedGraph query required)
  exact ⟨Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph domainEq agree, rfl⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.of_agreement_valid
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_output
