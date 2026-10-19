import InitECandidate.Solver.Mpt.WsAccountOptionalNormal
import InitECandidate.Solver.Mpt.WsAccountOptionalLeafImage

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Full unchanged original provider derives a physical account image on
present returns, alongside its actual retained allocation and source cost.
All empty-reference facts concern the current incoming environment. -/
theorem body_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff valueLimit : Nat) (data : WsAccountLeaf.Data source ws root heap nibs)
    (values : TrieWalk.Values data.graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad heap 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad heap query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad heap query)
    (rootProtection : Keccak256.Protected stp pad heap (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    Result post heap cursor limit returned ∧ HeapGlobals source post ∧ source.clock-post.clock≤191*valueLimit+2593 ∧
      (returned=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image post heap)) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat → Keccak256.Protected stp pad heap query →
        (∀ offset<64,query≠panByteAlignHOL (width:=64) (byteAddress nibs offset)) → post.memory query=source.memory query) := by
  obtain ⟨basic,room,price,nonheap⟩ := body_normal source post ws root addr heap nibs stp pad cursor limit cutoff valueLimit data values protectedValues hashData
    graphProtection valueProtection rootProtection addressCell arena heapGlobal heapBound heapLower heapAligned sizeBound aligned scratchBelow installed returned normal
  obtain ⟨allocated,ready,inner,answer,readyCell,result,readyArena,nextHeap,leafGlobals,leafMemory,codeEq,tailRun,restored⟩ :=
    body_leaf source post ws root addr heap nibs stp pad cursor limit cutoff valueLimit data values protectedValues hashData graphProtection valueProtection rootProtection
      addressCell arena heapGlobal heapBound installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  obtain ⟨image,window⟩ := after_leaf_image ready inner heap cursor limit emptyRoot emptyHash cutoff valueLimit answer readyCell result readyArena nextHeap heapBound heapLower heapAligned
    sizeBound aligned scratchBelow ((leafGlobals _ (by decide)).trans rootGlobal) ((leafGlobals _ (by decide)).trans hashGlobal)
    rootArena hashArena readyInstalled returned tailRun
  refine ⟨basic,nonheap,price,?_,?_⟩
  · rcases image with absent | image
    · exact Or.inl absent
    · right
      obtain ⟨present⟩ := image
      rw [restored]
      exact ⟨AccountDecode.Image.of_agreement inner _ heap present rfl (by rfl) (by rfl)⟩
  · intro query beyond below guarded outside
    rw [restored]
    exact (window query beyond below).trans (leafMemory query guarded outside)

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_image
