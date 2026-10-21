import InitECandidate.Solver.Mpt.WitnessCoreExtensionFrame
import InitECandidate.Solver.Mpt.TrieGraphRegister

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open WitnessRadix.QueryBranch

/-- The original extension's completed structural fields. Its compact
path is nonempty, as derived from the actual decoder guard. -/
structure ExtensionView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibbles length child : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena node 56
  aligned : node.toNat%8=0
  nodeFloor : 2713731432≤node.toNat
  pathArena : AllocatedBytes.Arena nibbles length.toNat
  pathPositive : 0<length.toNat
  pathBound : length.toNat≤2048
  cells : ∀ entry∈[(0,2#64),(32,nibbles),(40,length),(48,child)],
    source.memory (node+BitVec.ofNat 64 entry.1)=.word entry.2

def ExtensionView.path (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibbles length child : BitVec 64) (view : ExtensionView source node nibbles length child) :
    TrieWalk.PathView source.memory source.memaddrs node :=
  ⟨length,nibbles,
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 56 40 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (40,length) (by simp),
    by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 56 32 view.domain view.arena (by decide) view.aligned (by decide),
    view.cells (32,nibbles) (by simp),
    by have upper:=view.pathArena.upper; have bound:=Nat.min_le_left length.toNat 64; omega,
    fun offset inside=>AllocatedBytes.byte_mapped source nibbles length.toNat offset view.domain view.pathArena (inside.trans_le (Nat.min_le_left _ _))⟩

/-- Every initialized constructor field except the overwritten parent
metadata survives the real extension return and its scope restorations. -/
theorem extension_finished_constructor_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (field : FieldStores.Field) (member : field∈NodeConstructor.fields .extension (extensionWords nibbles length child))
    (away8 : BitVec.ofNat 64 field.offset≠8#64) (away16 : BitVec.ofNat 64 field.offset≠16#64) :
    (extensionFinishedState source heap nibbles length child previous kind data).memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  let ready:=QueryBranch.bind (extensionAllocated (QueryBranch.bind source "ck" kind) heap nibbles length child) "ex" heap
  change (metadataState ready heap data.pointer data.length previous).memory (heap+BitVec.ofNat 64 field.offset)=_
  rw [metadata_memory ready heap data.pointer data.length previous _
    (fun equal=>away8 ((BitVec.add_right_inj heap).mp equal))
    (fun equal=>away16 ((BitVec.add_right_inj heap).mp equal))]
  change WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child)))
    (heap+BitVec.ofNat 64 field.offset)=_
  exact WordWrites.write_unique source.memory _ _ (NodeConstructor.fields_distinct .extension _ heap) (List.mem_map.mpr ⟨field,member,rfl⟩)

theorem extension_finished_view (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.extension nibbles length)
    (nodeArena : AllocatedBytes.Arena heap 56) (aligned : heap.toNat%8=0) (lower : 2713731432≤heap.toNat) :
    ExtensionView (extensionFinishedState source heap nibbles length child previous kind data) heap nibbles length child := by
  have pathOwned:=view.owned
  simp only [payload,WitnessRecord.Payload.Owned] at pathOwned
  refine ⟨view.rows.domain,nodeArena,aligned,lower,pathOwned.2.2,pathOwned.1,pathOwned.2.1,?_⟩
  intro entry member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · simpa only [BitVec.add_zero] using extension_finished_tag source heap nibbles length child previous kind data
  · exact extension_finished_constructor_cell source heap nibbles length child previous kind data ⟨32,.saved "nib" nibbles⟩
      (by simp [NodeConstructor.fields,extensionWords]) (by change (32#64 : BitVec 64)≠8#64; decide) (by change (32#64 : BitVec 64)≠16#64; decide)
  · exact extension_finished_constructor_cell source heap nibbles length child previous kind data ⟨40,.saved "nlen" length⟩
      (by simp [NodeConstructor.fields,extensionWords]) (by change (40#64 : BitVec 64)≠8#64; decide) (by change (40#64 : BitVec 64)≠16#64; decide)
  · exact extension_finished_constructor_cell source heap nibbles length child previous kind data ⟨48,.saved "child" child⟩
      (by simp [NodeConstructor.fields,extensionWords]) (by change (48#64 : BitVec 64)≠8#64; decide) (by change (48#64 : BitVec 64)≠16#64; decide)

/-- The rich path/child contract follows the same genuine whole original
extension return as the physical-stack proof, including its real guards. -/
theorem return_extension_view_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.extension nibbles length)
    (topCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "result")=some (.val (.word child)))
    (previousCell : source.memory record=.word previous)
    (childMapped : source.memaddrs child) (kindCell : source.memory child=.word kind)
    (heapCell : source.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (heapLower : 2713731432≤heap.toNat) (before : data.BeforeHeap heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnExtension=(none,post)) :
    child≠0#64 ∧ (kind=0#64 ∨ kind=3#64) ∧ ExtensionView post heap nibbles length child := by
  obtain ⟨nonnull,supported,arena,funded,endpoint⟩ := return_extension_normal source post record db heap nibbles length child previous kind data
    view payload topCell resultCell previousCell childMapped kindCell heapCell heapArena heapAligned heapLower before installed normal
  exact ⟨nonnull,supported,by rw [endpoint]; exact extension_finished_view source record db heap nibbles length child previous kind data view payload arena heapAligned heapLower⟩

/-- Register the completed extension from actual current fields and its
already registered child. No input-graph acyclicity premise is needed. -/
def ExtensionView.registration (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibbles length child : BitVec 64) (view : ExtensionView source node nibbles length child)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) : TrieWalk.Registration graph node := by
  have tag : wordAt source.memory node=2#64 := by
    simp [wordAt,MemoryBytes.wordBits,show source.memory node=.word 2#64 from by simpa only [BitVec.add_zero] using view.cells (0,2#64) (by simp)]
  refine ⟨?_,by rw [tag]; simpa only [BitVec.add_zero] using view.cells (0,2#64) (by simp),fun _=>view.path source node nibbles length child,?_,?_,?_⟩
  · simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source node 56 0 view.domain view.arena (by decide) view.aligned (by decide)
  · intro extensionTag
    exact ⟨child,by simpa only [byteAddress] using AllocatedBytes.word_mapped source node 56 48 view.domain view.arena (by decide) view.aligned (by decide),
      view.cells (48,child) (by simp),member⟩
  · intro extensionTag zero
    have size : wordAt source.memory (node+40#64)=length := by simp [wordAt,view.cells (40,length) (by simp),MemoryBytes.wordBits]
    have eq : length=0#64 := size.symm.trans zero
    have positive:=view.pathPositive
    rw [eq] at positive
    exact (Nat.not_lt_zero _ positive).elim
  · intro notHash notLeaf notExtension
    exact (notExtension tag).elim

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_constructor_cell
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ExtensionView.registration

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_extension_view_normal
