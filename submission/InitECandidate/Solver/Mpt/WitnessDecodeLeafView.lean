import InitECandidate.Solver.Mpt.WitnessDecodeLeafCells
import InitECandidate.Solver.Mpt.TrieWalkValues

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Physical original decoded leaf data. The mutable hash cache at24 is
deliberately excluded. Path and value views below reuse the existing trie
walk model; no byte-content or input-acyclicity assumption is introduced. -/
structure LeafView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node db pointer length nibbles nibbleLength valuePointer valueLength : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena node 64
  aligned : node.toNat%8=0
  nodeFloor : 2713731432≤node.toNat
  cells : ∀ entry∈[(0,1#64),(8,pointer),(16,length),(32,nibbles),(40,nibbleLength),(48,valuePointer),(56,valueLength)],
    source.memory (node+BitVec.ofNat 64 entry.1)=.word entry.2
  parentArena : AllocatedBytes.Arena pointer length.toNat
  parentBound : length.toNat≤1024
  parentLower : 2713731432≤pointer.toNat
  parentBeforeDb : pointer.toNat+length.toNat≤db.toNat
  nibbleArena : AllocatedBytes.Arena nibbles nibbleLength.toNat
  nibbleBound : nibbleLength.toNat≤2048
  valueArena : AllocatedBytes.Arena valuePointer valueLength.toNat
  valueBound : valueLength.toNat≤1024
  valueLower : 2713731432≤valuePointer.toNat
  valueBeforeDb : valuePointer.toNat+valueLength.toNat≤db.toNat

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory}
  {node db pointer length nibbles nibbleLength valuePointer valueLength : BitVec 64}

theorem LeafView.tag (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength) :
    source.memory node=.word 1#64 := by
  simpa only [BitVec.add_zero] using view.cells (0,1#64) (by simp)

def LeafView.path (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength) :
    TrieWalk.PathView source.memory source.memaddrs node :=
  ⟨nibbleLength,nibbles,
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 64 40 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (40,nibbleLength) (by simp),
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 64 32 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (32,nibbles) (by simp),by have upper:=view.nibbleArena.upper; have small:=Nat.min_le_left nibbleLength.toNat 64; omega,
    fun offset inside=>AllocatedBytes.byte_mapped source nibbles nibbleLength.toNat offset view.domain view.nibbleArena (inside.trans_le (Nat.min_le_left _ _))⟩

def LeafView.value (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength) :
    TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 1024
      (fun p n=>2713731432≤p.toNat ∧ p.toNat+n.toNat≤db.toNat) :=
  ⟨valuePointer,valueLength,
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 64 48 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (48,valuePointer) (by simp),
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 64 56 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (56,valueLength) (by simp),
    ⟨view.valueBound,view.valueBeforeDb.trans_lt db.isLt,
      fun offset inside=>AllocatedBytes.byte_mapped source valuePointer valueLength.toNat offset view.domain view.valueArena inside⟩,
    view.valueLower,view.valueBeforeDb⟩

theorem LeafView.of_fields (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) :
    LeafView target node db pointer length nibbles nibbleLength valuePointer valueLength := by
  refine ⟨domain.trans view.domain,view.arena,view.aligned,view.nodeFloor,?_,view.parentArena,view.parentBound,view.parentLower,view.parentBeforeDb,
    view.nibbleArena,view.nibbleBound,view.valueArena,view.valueBound,view.valueLower,view.valueBeforeDb⟩
  intro entry member
  rw [memory]
  exact view.cells entry member

theorem leaf_view_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node db pointer length nibbles nibbleLength valuePointer valueLength : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (nodeArena : AllocatedBytes.Arena node 64) (aligned : node.toNat%8=0)
    (nodeFloor : 2713731432≤node.toNat)
    (parentArena : AllocatedBytes.Arena pointer length.toNat) (parentBound : length.toNat≤1024)
    (parentLower : 2713731432≤pointer.toNat) (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (nibbleArena : AllocatedBytes.Arena nibbles nibbleLength.toNat) (nibbleBound : nibbleLength.toNat≤2048)
    (valueArena : AllocatedBytes.Arena valuePointer valueLength.toNat) (valueBound : valueLength.toNat≤1024)
    (valueLower : 2713731432≤valuePointer.toNat) (valueBefore : valuePointer.toNat+valueLength.toNat≤db.toNat)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source node (leafWords nibbles nibbleLength valuePointer valueLength) with
        memory:=WordWrites.write (leafAllocated source node (leafWords nibbles nibbleLength valuePointer valueLength)).memory
          (LocalFields.writes node (leafFields (leafParentWords pointer length)))}) :
    LeafView target node db pointer length nibbles nibbleLength valuePointer valueLength := by
  have currentDomain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at currentDomain
  have constructed:=leaf_constructor_cells_of_post source target node (leafWords nibbles nibbleLength valuePointer valueLength) (leafParentWords pointer length) post
  have parents:=leaf_parent_cells_of_post source target node (leafWords nibbles nibbleLength valuePointer valueLength) (leafParentWords pointer length) post
  refine ⟨currentDomain.trans domain,nodeArena,aligned,nodeFloor,?_,parentArena,parentBound,parentLower,parentBefore,nibbleArena,nibbleBound,valueArena,valueBound,valueLower,valueBefore⟩
  intro entry member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact constructed ⟨0,.literal 1#64⟩ (by simp [NodeConstructor.fields]) (by decide) (by decide)
  · simpa only [LocalFields.Operand.word,leafParentWords] using parents ⟨8,.saved "p" pointer⟩ (by simp [leafFields,leafParentWords])
  · simpa only [LocalFields.Operand.word,leafParentWords] using parents ⟨16,.saved "n" length⟩ (by simp [leafFields,leafParentWords])
  · simpa only [FieldStores.Value.word,leafWords] using constructed ⟨32,.saved "nib" nibbles⟩ (by simp [NodeConstructor.fields,leafWords]) (by change 32≠8; decide) (by change 32≠16; decide)
  · simpa only [FieldStores.Value.word,leafWords] using constructed ⟨40,.saved "nlen" nibbleLength⟩ (by simp [NodeConstructor.fields,leafWords]) (by change 40≠8; decide) (by change 40≠16; decide)
  · simpa only [FieldStores.Value.word,leafWords] using constructed ⟨48,.saved "vptr" valuePointer⟩ (by simp [NodeConstructor.fields,leafWords]) (by change 48≠8; decide) (by change 48≠16; decide)
  · simpa only [FieldStores.Value.word,leafWords] using constructed ⟨56,.saved "vlen" valueLength⟩ (by simp [NodeConstructor.fields,leafWords]) (by change 56≠8; decide) (by change 56≠16; decide)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.tag
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.path
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.value
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_view_of_post
