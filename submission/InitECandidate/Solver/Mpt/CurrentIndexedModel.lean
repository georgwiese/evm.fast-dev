import InitECandidate.Solver.Mpt.IndexedSliceArray
import InitECandidate.Solver.Mpt.IndexedSetNormal
import InitECandidate.Solver.Input.CurrentRlp.WordWrite
import InitECandidate.Solver.MutableTable.MemoryRegionCore

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

abbrev keyPointer : BitVec 64:=2701134808#64

def NonemptyRow (pointer size : BitVec 64) : Prop:=pointer≠0#64 ∧ size≠0#64

/-- Current fresh unsecured indexed-trie loop. Original rows stay before
its header, while live nodes and paths stay beyond its aligned cutoff.
There is no secure-hash oracle or historical scratch-arena hypothesis. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) where
  index : BitVec 64
  root : BitVec 64
  heap : BitVec 64
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array))
  bounded : index.toNat≤count
  countBound : count<2^64
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  installed : OriginalCode.Installed source.code
  keyGlobal : source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word keyPointer))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  floor : cutoff≤heap.toNat
  headerArena : AllocatedBytes.Arena m 16
  headerAligned : m.toNat%8=0
  headerAbove : 2701134824≤m.toNat
  headerBefore : m.toNat+16≤cutoff
  cutoffAligned : cutoff%8=0
  rootStored : source.memory m=.word root
  flagStored : source.memory (m+8#64)=.word 0#64
  rows : Indexed.SliceArray source array count m.toNat limit slices NonemptyRow
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  rootUncached : TrieWalk.Uncached source.memory root
  values : TrieWalk.Values graph limit (fun _ _=>True)
  regions : graph.Regions cutoff heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions cutoff heap.toNat
  separated : graph.PathSeparated

/-- A real scoped current RLP key return retains all nonlocals and every
word outside the actual16-byte startup workspace. -/
theorem key_returned {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (index : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (keyGlobal : source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word keyPointer)))
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (reached : CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments) target) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ target.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ name,name≠ofString "klen"→target.locals.lookup name=source.locals.lookup name) ∧
      source.clock-target.clock≤19 ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,(query.toNat<2701134808 ∨ 2701134824≤query.toNat)→target.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Indexed.keyArguments=
      some [.val (.word keyPointer),.val (.word index)]:=by
    simp [Indexed.keyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,keyGlobal,iCell]
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup keyPointer index (CurrentRlp.WordWrite.original_code source.code installed)
  obtain ⟨child,returned,run,endpoint⟩:=reached.scoped_known (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments _
    CurrentRlp.WordWrite.body callee .one args called
  obtain ⟨encoded,lower,upper,answer,price,frame⟩:=CurrentRlp.WordWrite.body_normal (callEntryStateHOLFinite source callee) child keyPointer index installed d w returned run
  rw [endpoint,answer]
  refine ⟨encoded,lower,upper,?_,?_,?_,frame.metadata,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro name other
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  · change source.clock-1-child.clock≤18 at price
    change source.clock-child.clock≤19
    omega
  · intro query outside
    apply frame.memory query
    exact MutableTable.MemoryRegion.copy_away ⟨2701134808,16⟩ ⟨by decide,by decide,by decide⟩ 9 (by decide) query outside

/-- Actual RLP key conversion retains the complete current indexed-loop
state and original rows, with the real returned encoded length. -/
theorem key_model {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices)
    (reached : CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments) target) :
    ∃ encoded : Nat,∃ next : LoopModel target m array count cutoff limit slices,
      1≤encoded ∧ encoded≤9 ∧ target.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      next.index=model.index ∧ next.root=model.root ∧ next.heap=model.heap ∧ source.clock-target.clock≤19 := by
  obtain ⟨encoded,lower,upper,cell,saved,price,frame,memory⟩:=key_returned model.index model.installed model.keyGlobal model.indexCell reached
  have domain:=MemoryMetadata.domain frame
  have endian:=MemoryMetadata.endian frame
  have codeEq:=MemoryMetadata.code frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  have agree (query : BitVec 64) (above : 2701134824≤query.toNat) : target.memory query=source.memory query:=memory query (Or.inr above)
  have floor : 2701134824≤cutoff:=by have a:=model.headerAbove; have b:=model.headerBefore; omega
  obtain ⟨graph,same,regions,disjoint,values,paths,pathRegions,separated⟩:=model.graph.after_path_band source target limit cutoff cutoff model.heap.toNat 2701134824
    (fun _ _=>True) model.values model.regions model.disjoint model.paths model.pathRegions model.separated (by decide) floor floor domain endian
    (fun query above before=>agree query above)
  have flagNumber : (m+8#64).toNat=m.toNat+8:=byteAddress_toNat m 8 (by have upper:=model.headerArena.upper; omega)
  let next : LoopModel target m array count cutoff limit slices:={
    index:=model.index,root:=model.root,heap:=model.heap
    indexCell:=(saved _ (by decide)).trans model.indexCell,countCell:=(saved _ (by decide)).trans model.countCell
    mCell:=(saved _ (by decide)).trans model.mCell,arrayCell:=(saved _ (by decide)).trans model.arrayCell
    bounded:=model.bounded,countBound:=model.countBound,domain:=domain.trans model.domain,little:=endian.trans model.little
    installed:=by rw [codeEq]; exact model.installed
    keyGlobal:=by rw [globals]; exact model.keyGlobal
    heapCell:=by rw [globals]; exact model.heapCell
    heapArena:=model.heapArena,heapAligned:=model.heapAligned,floor:=model.floor
    headerArena:=model.headerArena,headerAligned:=model.headerAligned,headerAbove:=model.headerAbove,headerBefore:=model.headerBefore,cutoffAligned:=model.cutoffAligned
    rootStored:=(agree m model.headerAbove).trans model.rootStored
    flagStored:=(agree (m+8#64) (by rw [flagNumber]; have lower:=model.headerAbove; omega)).trans model.flagStored
    rows:=model.rows.of_band source target array count m.toNat limit slices NonemptyRow domain (fun query above before=>agree query above)
    graph:=graph,member:=by rw [same]; exact model.member
    rootUncached:=(model.graph.cache_of_band cutoff model.heap.toNat model.regions (fun query above _before=>agree query (Nat.le_trans floor above))).uncached model.graph model.root model.member model.rootUncached
    values:=Classical.choice values,regions:=regions,disjoint:=disjoint,paths:=paths,pathRegions:=pathRegions,separated:=separated }
  exact ⟨encoded,next,lower,upper,cell,rfl,rfl,rfl,price⟩

/-- Local counter assignments, call restoration and lexical exits retain
all nonlocal loop data. The actual new counter cells are supplied explicitly. -/
theorem LoopModel.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (index : BitVec 64) (bounded : index.toNat≤count)
    (frame : LocalEffects.erase target=LocalEffects.erase source)
    (indexCell : target.locals.lookup (ofString "i")=some (.val (.word index)))
    (countCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (mCell : target.locals.lookup (ofString "m")=some (.val (.word m)))
    (arrayCell : target.locals.lookup (ofString "slice_arr")=some (.val (.word array))) :
    ∃ next : LoopModel target m array count cutoff limit slices,next.index=index ∧ next.root=model.root ∧ next.heap=model.heap := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have metadata:=MemoryMetadata.of_frame frame
  have domain:=MemoryMetadata.domain metadata
  have endian:=MemoryMetadata.endian metadata
  have codeEq:=MemoryMetadata.code metadata
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  obtain ⟨graph,same,regions,disjoint,values,paths,pathRegions,separated⟩:=model.graph.after_erase source target limit cutoff model.heap.toNat cutoff model.heap.toNat
    (fun _ _=>True) model.values model.regions model.disjoint model.paths model.pathRegions model.separated frame
  let next : LoopModel target m array count cutoff limit slices:={
    index:=index,root:=model.root,heap:=model.heap,indexCell:=indexCell,countCell:=countCell,mCell:=mCell,arrayCell:=arrayCell
    bounded:=bounded,countBound:=model.countBound,domain:=domain.trans model.domain,little:=endian.trans model.little
    installed:=by rw [codeEq]; exact model.installed
    keyGlobal:=by rw [globals]; exact model.keyGlobal
    heapCell:=by rw [globals]; exact model.heapCell
    heapArena:=model.heapArena,heapAligned:=model.heapAligned,floor:=model.floor
    headerArena:=model.headerArena,headerAligned:=model.headerAligned,headerAbove:=model.headerAbove,headerBefore:=model.headerBefore,cutoffAligned:=model.cutoffAligned
    rootStored:=(congrFun memory m).trans model.rootStored,flagStored:=(congrFun memory (m+8#64)).trans model.flagStored
    rows:=model.rows.of_band source target array count m.toNat limit slices NonemptyRow domain (fun query above before=>congrFun memory query)
    graph:=graph,member:=by rw [same]; exact model.member
    rootUncached:=by rw [memory]; exact model.rootUncached
    values:=Classical.choice values,regions:=regions,disjoint:=disjoint,paths:=paths,pathRegions:=pathRegions,separated:=separated }
  exact ⟨next,rfl,rfl,rfl⟩

end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.key_returned
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.key_model

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.LoopModel.of_frame
