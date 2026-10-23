import InitECandidate.Solver.Mpt.TrieGraphChildWord
import InitECandidate.Solver.Mpt.TrieChildSlot
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- An original extension/branch child store preserves the whole live
graph, values, full nibble buffers and their ownership. The replacement
child must already be registered; shared children are allowed. -/
theorem Graph.after_child_store (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (owner child : BitVec 64) (offset : Nat) (slot : ChildSlot source.memory owner offset)
    (ownerMember : graph.valid owner) (ownerActive : owner≠0#64) (childMember : graph.valid child) :
    let post:={source with memory:=StoreWord.put source.memory (owner+BitVec.ofNat 64 offset) child}
    ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  let address:=owner+BitVec.ofNat 64 offset
  let post:={source with memory:=StoreWord.put source.memory address child}
  have headers : ∀ node,graph.valid node → node≠0#64 → post.memory node=source.memory node:=by
    intro node member active
    exact if_neg (graph.child_store_header_away lower upper regions disjoint owner offset slot ownerMember ownerActive node member active)
  have pathWords : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      post.memory (node+32#64)=source.memory (node+32#64) ∧ post.memory (node+40#64)=source.memory (node+40#64):=by
    intro node member active tag
    have away:=graph.child_store_path_away lower upper regions disjoint owner offset slot ownerMember ownerActive node member active tag
    exact ⟨if_neg away.1,if_neg away.2⟩
  let next:=graph.of_child_word source.memory source.memaddrs source.be paths address child childMember headers pathWords
  have validEq : next.valid=graph.valid:=rfl
  have fields : graph.PathFields post.memory:=by
    constructor
    · intro node member active
      exact congrArg MemoryBytes.wordBits (headers node member active)
    · intro node member active tag
      have words:=pathWords node member active tag
      exact ⟨congrArg MemoryBytes.wordBits words.1,congrArg MemoryBytes.wordBits words.2⟩
  have valueWords : ∀ query,ValueFootprint graph query → post.memory query=source.memory query:=by
    intro query required
    exact if_neg (graph.child_store_value_away lower upper regions disjoint owner offset slot ownerMember ownerActive query required)
  let nextValues:=Values.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next limit values validEq rfl fields.tags valueWords
  have byteWords : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    exact if_neg (separated node member active tag index inside owner ownerMember ownerActive offset (slot.bounds source.memory owner offset).2.2.1)
  exact ⟨next,validEq,regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next lower upper validEq fields.tags,
    disjoint.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq fields.tags,⟨nextValues⟩,
    paths.of_fields source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next validEq rfl rfl fields byteWords,
    pathRegions.of_fields source.memory post.memory source.memaddrs post.memaddrs graph next pathLower pathUpper validEq fields,
    separated.of_fields source.memory post.memory source.memaddrs post.memaddrs graph next validEq fields⟩

/-- Independent query and split buffers survive these same actual child
stores, including unaligned borrowed suffixes. -/
theorem Graph.PathBuffer.after_child_store (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (lower upper : Nat) (pointer : BitVec 64) (length : Nat)
    (buffer : graph.PathBuffer source.be lower upper pointer length)
    (owner child : BitVec 64) (offset : Nat) (slot : ChildSlot source.memory owner offset)
    (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (next : Graph (StoreWord.put source.memory (owner+BitVec.ofNat 64 offset) child) source.memaddrs)
    (validEq : next.valid=graph.valid)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt (StoreWord.put source.memory (owner+BitVec.ofNat 64 offset) child) node=wordAt source.memory node) :
    next.PathBuffer source.be lower upper pointer length := by
  refine ⟨?_,buffer.bounds,?_⟩
  · apply buffer.span.of_agreement source.memory _ source.memaddrs source.memaddrs source.be source.be pointer length rfl rfl
    intro index inside
    exact if_neg (buffer.apart index inside owner ownerMember ownerActive offset (slot.bounds source.memory owner offset).2.2.1)
  · intro index inside node member active field within
    have oldMember : graph.valid node:=by rwa [validEq] at member
    rw [tags node oldMember active] at within
    exact buffer.apart index inside node oldMember active field within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_child_store
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.after_child_store
