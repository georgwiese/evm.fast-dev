import InitECandidate.Solver.Mpt.TrieGraphCacheOffsets
import InitECandidate.Solver.Mpt.TrieChildSlot
import InitECandidate.Solver.Mpt.TrieParentSlot
import InitECandidate.Solver.Mpt.NodeConstructorPhysicalFrame
import InitECandidate.Solver.Mpt.NodeInvalidate
import InitECandidate.Solver.Mpt.LeafUpdateProgram
import InitECandidate.Solver.Mpt.BranchValueUpdateProgram

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real nonempty root has neither an encoded RLP pointer nor a hash
pointer. No claim is made about the irrelevant saved length at offset16. -/
def Uncached (memory : Memory) (node : BitVec 64) : Prop :=
  node=0#64 ∨ memory (node+8#64)=.word 0#64 ∧ memory (node+24#64)=.word 0#64

/-- Insertions may invalidate existing caches. This records preservation
of their zero values, without assuming that an arbitrary decoded graph
started with empty caches. -/
def Graph.CacheFrame {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (nextMemory : Memory) : Prop :=
  ∀ node,graph.valid node→node≠0#64→∀ offset : Nat,(offset=8 ∨ offset=24)→
    memory (node+BitVec.ofNat 64 offset)=.word 0#64→nextMemory (node+BitVec.ofNat 64 offset)=.word 0#64

theorem Graph.CacheFrame.refl {memory : Memory} {domain : BitVec 64→Prop} (graph : Graph memory domain) :
    graph.CacheFrame memory := by
  intro node member active offset cache zero
  exact zero

theorem Graph.CacheFrame.trans {memory middle last : Memory} {domain middleDomain : BitVec 64→Prop}
    (graph : Graph memory domain) (next : Graph middle middleDomain)
    (first : graph.CacheFrame middle) (second : next.CacheFrame last)
    (members : ∀ node,graph.valid node→next.valid node) : graph.CacheFrame last := by
  intro node member active offset cache zero
  exact second node (members node member) active offset cache (first node member active offset cache zero)

theorem Graph.CacheFrame.uncached {memory nextMemory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (frame : graph.CacheFrame nextMemory) (node : BitVec 64)
    (member : graph.valid node) (clean : Uncached memory node) : Uncached nextMemory node := by
  rcases clean with zero|⟨rlp,hash⟩
  · exact Or.inl zero
  · by_cases zero : node=0#64
    · exact Or.inl zero
    · exact Or.inr ⟨frame node member zero 8 (Or.inl rfl) rlp,frame node member zero 24 (Or.inr rfl) hash⟩

/-- A zero store preserves every already zero cache even when its address
is exactly that cache. This includes the real invalidation stores. -/
theorem Graph.cache_zero_store {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query : BitVec 64) :
    graph.CacheFrame (StoreWord.put memory query 0#64) := by
  intro node member active offset cache zero
  unfold StoreWord.put
  split
  · rfl
  · exact zero

/-- Every actual structural/value field is separated from every cache
word by the real node allocation geometry. -/
theorem Graph.cache_data_store {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner : BitVec 64) (offset : Nat) (value : BitVec 64) (member : graph.valid owner) (active : owner≠0#64)
    (inside : offset<nodeBytes (wordAt memory owner)) (data : offset=0 ∨ 32≤offset) :
    graph.CacheFrame (StoreWord.put memory (owner+BitVec.ofNat 64 offset) value) := by
  intro node nodeMember nodeActive cache cacheOffset zero
  have away:=graph.cache_field_away lower upper regions disjoint node owner offset cache
    (by rcases cacheOffset with rfl|rfl <;> decide) (by rcases cacheOffset with rfl|rfl <;> decide)
    nodeMember nodeActive member active inside data
  exact (if_neg away.symm).trans zero

theorem Graph.cache_child_store {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner child : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset)
    (member : graph.valid owner) (active : owner≠0#64) :
    graph.CacheFrame (StoreWord.put memory (owner+BitVec.ofNat 64 offset) child) := by
  have bounds:=slot.bounds memory owner offset
  exact graph.cache_data_store lower upper regions disjoint owner offset child member active bounds.2.2.1 (Or.inr bounds.1)

theorem Graph.ParentSlot.cache_away {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (address node : BitVec 64) (slot : graph.ParentSlot address) (member : graph.valid node) (active : node≠0#64)
    (cache : Nat) (offset : cache=8 ∨ cache=24) : address≠0#64→node+BitVec.ofNat 64 cache≠address := by
  intro nonzero
  rcases slot with zero|⟨owner,field,ownerMember,ownerActive,selected,equal⟩
  · exact (nonzero zero).elim
  · rw [equal]
    have bounds:=selected.bounds memory owner field
    exact (graph.cache_field_away lower upper regions disjoint node owner field cache
      (by rcases offset with rfl|rfl <;> decide) (by rcases offset with rfl|rfl <;> decide)
      member active ownerMember ownerActive bounds.2.2.1 (Or.inr bounds.1)).symm

theorem Graph.cache_invalidate (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (owner : BitVec 64) :
    graph.CacheFrame (NodeInvalidate.post source owner).memory := by
  intro node member active offset cache zero
  simp only [NodeInvalidate.post,NodeInvalidate.fields,FieldStores.writes,List.map_cons,List.map_nil,
    FieldStores.Value.word,WordWrites.write,StoreWord.put]
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  split <;> first | rfl | exact zero

theorem invalidate_uncached (source : PanSemStateFiniteExact 64 Guest.HostMemory) (owner : BitVec 64) :
    Uncached (NodeInvalidate.post source owner).memory owner := by
  apply Or.inr
  simp [Uncached,NodeInvalidate.post,NodeInvalidate.fields,FieldStores.writes,WordWrites.write,StoreWord.put,
    FieldStores.Value.word,BitVec.add_right_inj]

theorem Graph.cache_leaf_update (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner pointer size : BitVec 64) (member : graph.valid owner) (active : owner≠0#64) (leaf : wordAt source.memory owner=1#64) :
    graph.CacheFrame (InsertLeaf.post source owner pointer size).memory := by
  intro node nodeMember nodeActive cache cacheOffset zero
  have away (offset : Nat) (inside : offset<64) (data : 32≤offset) : node+BitVec.ofNat 64 cache≠owner+BitVec.ofNat 64 offset:=by
    exact (graph.cache_field_away lower upper regions disjoint node owner offset cache
      (by rcases cacheOffset with rfl|rfl <;> decide) (by rcases cacheOffset with rfl|rfl <;> decide)
      nodeMember nodeActive member active (by rw [leaf]; exact inside) (Or.inr data)).symm
  exact (InsertLeaf.post_away source owner pointer size _ (away 48 (by decide) (by decide)) (away 56 (by decide) (by decide))).trans zero

theorem Graph.cache_branch_value (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner pointer size : BitVec 64) (member : graph.valid owner) (active : owner≠0#64) (branch : wordAt source.memory owner=3#64) :
    graph.CacheFrame (BranchValueUpdate.post source owner pointer size).memory := by
  intro node nodeMember nodeActive cache cacheOffset zero
  have away (offset : Nat) (inside : offset<176) (data : 32≤offset) : node+BitVec.ofNat 64 cache≠owner+BitVec.ofNat 64 offset:=by
    exact (graph.cache_field_away lower upper regions disjoint node owner offset cache
      (by rcases cacheOffset with rfl|rfl <;> decide) (by rcases cacheOffset with rfl|rfl <;> decide)
      nodeMember nodeActive member active (by rw [branch]; exact inside) (Or.inr data)).symm
  exact (BranchValueUpdate.post_away source owner pointer size _ (away 160 (by decide) (by decide)) (away 168 (by decide) (by decide))).trans zero

theorem Graph.cache_branch_value_of_tags (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner pointer size : BitVec 64) (member : graph.valid owner) (active : owner≠0#64)
    (notHash : wordAt source.memory owner≠0#64) (notLeaf : wordAt source.memory owner≠1#64) (notExtension : wordAt source.memory owner≠2#64) :
    graph.CacheFrame (BranchValueUpdate.post source owner pointer size).memory := by
  intro node nodeMember nodeActive cache cacheOffset zero
  have away (offset : Nat) (inside : offset<176) (data : 32≤offset) : node+BitVec.ofNat 64 cache≠owner+BitVec.ofNat 64 offset:=by
    exact (graph.cache_field_away lower upper regions disjoint node owner offset cache
      (by rcases cacheOffset with rfl|rfl <;> decide) (by rcases cacheOffset with rfl|rfl <;> decide)
      nodeMember nodeActive member active (by simpa [nodeBytes,notHash,notLeaf,notExtension] using inside) (Or.inr data)).symm
  exact (BranchValueUpdate.post_away source owner pointer size _ (away 160 (by decide) (by decide)) (away 168 (by decide) (by decide))).trans zero

/-- Fresh constructor writes cannot reach any cache in an older allocated
node. The upper frontier bounds the complete node, including both caches. -/
theorem Graph.cache_of_older {memory nextMemory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (older : ∀ query : BitVec 64,query.toNat<upper→nextMemory query=memory query) : graph.CacheFrame nextMemory := by
  intro node member active offset cache zero
  obtain ⟨above,arena,aligned,before⟩:=regions node member active
  have size:=nodeBytes_bounds (wordAt memory node)
  have number:=byteAddress_toNat node offset (by have bounded:=arena.upper; rcases cache with rfl|rfl <;> omega)
  change (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset at number
  exact (older _ (by rw [number]; rcases cache with rfl|rfl <;> omega)).trans zero

theorem Graph.cache_of_band {memory nextMemory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (agree : ∀ query : BitVec 64,lower≤query.toNat→query.toNat<upper→nextMemory query=memory query) : graph.CacheFrame nextMemory := by
  intro node member active offset cache zero
  obtain ⟨above,arena,aligned,before⟩:=regions node member active
  have size:=nodeBytes_bounds (wordAt memory node)
  have number:=byteAddress_toNat node offset (by have bounded:=arena.upper; rcases cache with rfl|rfl <;> omega)
  change (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset at number
  exact (agree _ (by rw [number]; omega) (by rw [number]; rcases cache with rfl|rfl <;> omega)).trans zero

end InitECandidate.Solver.Mpt.TrieWalk

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem Physical.uncached {kind : Kind} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {heap : BitVec 64} {words : String→BitVec 64} (physical : Physical kind source target heap words)
    (fresh : kind=.leaf ∨ kind=.extension) : TrieWalk.Uncached target.memory heap := by
  apply Or.inr
  have rlp : (⟨8,.literal 0#64⟩ : FieldStores.Field)∈fields kind words:=by rcases fresh with rfl|rfl <;> simp [fields]
  have hash : (⟨24,.literal 0#64⟩ : FieldStores.Field)∈fields kind words:=by rcases fresh with rfl|rfl <;> simp [fields]
  exact ⟨physical.cells _ rlp,physical.cells _ hash⟩

theorem BranchPhysical.uncached {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {heap : BitVec 64} (physical : BranchPhysical source target heap) : TrieWalk.Uncached target.memory heap := by
  exact Or.inr ⟨physical.zeros 8 (by decide) (by decide) (by decide),physical.zeros 24 (by decide) (by decide) (by decide)⟩

theorem Physical.cache_frame {kind : Kind} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {heap : BitVec 64} {words : String→BitVec 64} (physical : Physical kind source target heap words)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (lower : Nat) (regions : graph.Regions lower heap.toNat) :
    graph.CacheFrame target.memory := by
  exact graph.cache_of_older lower heap.toNat regions (fun query before=>physical.memory query (Or.inl before))

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_data_store
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_child_store
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_invalidate
#print axioms InitECandidate.Solver.Mpt.TrieWalk.invalidate_uncached
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_leaf_update
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_branch_value
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.Physical.uncached
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.BranchPhysical.uncached
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.Physical.cache_frame
