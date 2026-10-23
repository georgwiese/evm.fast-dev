import InitECandidate.Solver.Mpt.IndexedLoopModel
import InitECandidate.Solver.Mpt.SetCall
import InitECandidate.Solver.Mpt.SetPersistentPrefix

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine indexed setter call derives its new live trie and map
header while preserving every input row for all subsequent iterations. -/
theorem set_model (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m array : BitVec 64) (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count)
    (encoded : Nat) (small : encoded≤9)
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (normal : evaluateHOLFiniteState source setCall=(none,target)) :
    ∃ next : LoopModel target m array count cutoff limit slices property,
      next.index=model.index ∧ model.heap.toNat≤next.heap.toNat ∧ source.clock-target.clock≤SetTrie.bodyAllowance cutoff+1 ∧
      (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query) := by
  have cutoffFloor : DeleteFrame.ceiling≤cutoff:=by have h:=model.cutoffLower; change 2713717616≤cutoff; omega
  have headerFloor : DeleteFrame.ceiling≤m.toNat:=cutoffFloor.trans model.headerAbove
  have rootMapped : source.memaddrs m:=by
    simpa [byteAddress] using AllocatedBytes.word_mapped source m 16 0 model.domain model.header.arena (by decide) model.header.aligned (by decide)
  have flagMapped:=AllocatedBytes.word_mapped source m 16 8 model.domain model.header.arena (by decide) model.header.aligned (by decide)
  have inputArena : AllocatedBytes.Arena 2713717624#64 encoded:=⟨by decide,by change 2713717624+encoded≤33806089496; omega⟩
  have inputBefore : (2713717624#64 : BitVec 64).toNat+encoded≤model.heap.toNat:=by have a:=model.cutoffLower; have b:=model.floor; change 2713717624+encoded≤model.heap.toNat; omega
  have hashArena : AllocatedBytes.Arena 2713717584#64 32:=⟨by decide,by decide⟩
  have hashBefore : (2713717584#64 : BitVec 64).toNat+32≤model.heap.toNat:=by have a:=model.cutoffLower; have b:=model.floor; change 2713717616≤model.heap.toNat; omega
  have hashCell:=model.bindings .hash
  have data:=Keccak256.allocated_entry source 2713714976#64 2713717624#64 2713715176#64 2713717584#64 encoded model.hash
    ⟨⟨by decide,by decide⟩,by decide,inputArena,⟨by decide,by decide⟩,by decide,hashArena⟩
  have args:=set_arguments source array m model.index count cutoff limit encoded slices property model.rows inside model.domain
    model.arrayCell model.mCell model.indexCell lengthCell (model.bindings .key)
  have owned : (slices model.index.toNat).1≠0#64→(slices model.index.toNat).2≠0#64→
      TrieWalk.Payload source.memaddrs (slices model.index.toNat).1 (slices model.index.toNat).2 limit ∧ property (slices model.index.toNat).1 (slices model.index.toNat).2:=by
    intro _ _; exact ⟨model.rows.payload model.index.toNat inside,model.rows.extra model.index.toNat inside⟩
  obtain ⟨locals,⟨output⟩⟩:=SetTrie.call_normal source target m 0#64 model.root 2713717624#64 2713714976#64 2713715176#64 2713717584#64 model.heap 2713714688#64 2701135872#64
    (slices model.index.toNat).1 (slices model.index.toNat).2 encoded (by omega) model.graph limit cutoff cutoff property
    model.values model.regions model.disjoint model.paths model.pathRegions model.separated model.header.member model.empty owned
    rootMapped model.header.rootStored flagMapped model.header.flagStored headerFloor (by have before:=model.headerBefore; omega) model.header.rootSafe hashCell data hashArena hashBefore inputArena inputBefore (by decide) (by decide) (by decide)
    model.heapCell model.heapArena model.heapAligned model.scratch (by decide) cutoffFloor (Nat.le_refl _) model.floor model.little model.installed setArguments args normal
  have bounded:=NibbleKey.nibble_length_bound 0#64 encoded (by omega)
  have lengthNumber : (BitVec.ofNat 64 (NibbleKey.nibbleLength 0#64 encoded)).toNat≤64:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; exact bounded
  have header:=model.header.after_set source target (.val (.word 0#64)) m model.root 0#64 model.heap _ model.graph limit cutoff cutoff property (SetTrie.bodyAllowance cutoff+1)
    output model.heapArena model.heapAligned lengthNumber headerFloor model.headerBefore
  have band:=output.persistent_prefix source target (.val (.word 0#64)) m model.heap _ model.graph limit cutoff cutoff cutoff property (SetTrie.bodyAllowance cutoff+1)
    model.heapArena model.heapAligned lengthNumber model.regions model.paths model.pathRegions model.cutoffAligned (Nat.le_refl _) (Nat.le_refl _) model.floor model.headerAbove
  have rows:=model.rows.of_band source target array count cutoff limit slices property output.domain (by
    intro query above before
    exact band query (by change 2713717616≤query.toNat; omega) before)
  have scratch : Rlp.Validation.Arena target 2713714688#64 2701135872#64:={
    domain:=output.domain.trans model.scratch.domain
    cursorGlobal:=(output.globalsNonHeap _ (by decide)).trans model.scratch.cursorGlobal
    limitGlobal:=(output.globalsNonHeap _ (by decide)).trans model.scratch.limitGlobal
    ordered:=model.scratch.ordered
    aligned:=model.scratch.aligned
    lower:=model.scratch.lower
    upper:=model.scratch.upper }
  let next : LoopModel target m array count cutoff limit slices property:={ model with
    root:=output.root
    heap:=output.heap
    indexCell:=by rw [locals]; exact model.indexCell
    countCell:=by rw [locals]; exact model.countCell
    mCell:=by rw [locals]; exact model.mCell
    arrayCell:=by rw [locals]; exact model.arrayCell
    floor:=model.floor.trans output.grows
    headerBefore:=model.headerBefore.trans output.grows
    domain:=output.domain.trans model.domain
    little:=output.endian.trans model.little
    installed:=by rw [output.code]; exact model.installed
    bindings:=model.bindings.of_heap_globals source target output.globalsNonHeap
    hash:=model.hash.after_execution source target 2713714976#64 2713715176#64 setCall none normal output.globalsNonHeap
    scratch:=scratch
    heapCell:=output.heapCell
    heapArena:=output.heapArena
    heapAligned:=output.heapAligned
    rows:=rows
    graph:=output.next
    values:=output.values
    regions:=output.regions
    disjoint:=output.disjoint
    paths:=output.paths
    pathRegions:=output.pathRegions
    separated:=output.separated
    header:=header }
  exact ⟨next,rfl,output.grows,output.price,by intro query above before; exact band query (by change 2713717616≤query.toNat; omega) before⟩

/-- Every actual indexed setter outcome is priced from its current
live map and actual selected row, including deletion and failed calls. -/
theorem set_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m array : BitVec 64) (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count)
    (encoded : Nat) (small : encoded≤9)
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded)))) :
    source.clock-(evaluateHOLFiniteState source setCall).2.clock≤SetTrie.bodyAllowance cutoff+1 := by
  have cutoffFloor : DeleteFrame.ceiling≤cutoff:=by have h:=model.cutoffLower; change 2713717616≤cutoff; omega
  have headerFloor : DeleteFrame.ceiling≤m.toNat:=cutoffFloor.trans model.headerAbove
  have rootMapped : source.memaddrs m:=by
    simpa [byteAddress] using AllocatedBytes.word_mapped source m 16 0 model.domain model.header.arena (by decide) model.header.aligned (by decide)
  have flagMapped:=AllocatedBytes.word_mapped source m 16 8 model.domain model.header.arena (by decide) model.header.aligned (by decide)
  have inputArena : AllocatedBytes.Arena 2713717624#64 encoded:=⟨by decide,by change 2713717624+encoded≤33806089496; omega⟩
  have inputBefore : (2713717624#64 : BitVec 64).toNat+encoded≤model.heap.toNat:=by have a:=model.cutoffLower; have b:=model.floor; change 2713717624+encoded≤model.heap.toNat; omega
  have hashArena : AllocatedBytes.Arena 2713717584#64 32:=⟨by decide,by decide⟩
  have hashBefore : (2713717584#64 : BitVec 64).toNat+32≤model.heap.toNat:=by have a:=model.cutoffLower; have b:=model.floor; change 2713717616≤model.heap.toNat; omega
  have hashCell:=model.bindings .hash
  have data:=Keccak256.allocated_entry source 2713714976#64 2713717624#64 2713715176#64 2713717584#64 encoded model.hash
    ⟨⟨by decide,by decide⟩,by decide,inputArena,⟨by decide,by decide⟩,by decide,hashArena⟩
  have args:=set_arguments source array m model.index count cutoff limit encoded slices property model.rows inside model.domain
    model.arrayCell model.mCell model.indexCell lengthCell (model.bindings .key)
  have owned : (slices model.index.toNat).1≠0#64→(slices model.index.toNat).2≠0#64→
      TrieWalk.Payload source.memaddrs (slices model.index.toNat).1 (slices model.index.toNat).2 limit ∧ property (slices model.index.toNat).1 (slices model.index.toNat).2:=by
    intro _ _; exact ⟨model.rows.payload model.index.toNat inside,model.rows.extra model.index.toNat inside⟩
  exact SetTrie.call_cost source m 0#64 model.root 2713717624#64 2713714976#64 2713715176#64 2713717584#64 model.heap 2713714688#64 2701135872#64
    (slices model.index.toNat).1 (slices model.index.toNat).2 encoded (by omega) model.graph limit cutoff cutoff property
    model.values model.regions model.disjoint model.paths model.pathRegions model.separated model.header.member model.empty owned
    rootMapped model.header.rootStored flagMapped model.header.flagStored headerFloor (by have before:=model.headerBefore; omega) hashCell data hashArena hashBefore inputArena inputBefore (by decide) (by decide) (by decide)
    model.heapCell model.heapArena model.heapAligned model.scratch (by decide) cutoffFloor (Nat.le_refl _) model.floor model.little model.installed (some none) setArguments args

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.set_model
#print axioms InitECandidate.Solver.Mpt.Indexed.set_cost
