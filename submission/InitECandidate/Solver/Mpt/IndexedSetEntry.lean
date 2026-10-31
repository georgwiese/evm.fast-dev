import InitECandidate.Solver.Mpt.SetEnvironment
import InitECandidate.Solver.Mpt.NibbleKeyUnsecuredGraph

namespace InitECandidate.Solver.Mpt.IndexedSet
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- A reached setter on the fresh unsecured indexed trie. All nodes and
borrowed paths lie beyond its earlier two-word header. Payload ownership
and nonemptiness describe the actual current row, not a future return.
The pure value property is retained through conversion and insertion. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m rawKey : BitVec 64) (byteLength : Nat) (pointer size : BitVec 64) (cutoff limit : Nat)
    (property : BitVec 64→BitVec 64→Prop := fun _ _=>True) where
  root : BitVec 64
  heap : BitVec 64
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word rawKey))
  lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 byteLength)))
  pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer))
  sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))
  small : byteLength≤32
  pointerActive : pointer≠0#64
  sizeActive : size≠0#64
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  installed : Input.OriginalCode.Installed source.code
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  inputArena : AllocatedBytes.Arena rawKey byteLength
  inputBefore : rawKey.toNat+byteLength≤heap.toNat
  headerArena : AllocatedBytes.Arena m 16
  headerAligned : m.toNat%8=0
  headerBefore : m.toNat+16≤cutoff
  cutoffAligned : cutoff%8=0
  floor : cutoff≤heap.toNat
  rootStored : source.memory m=.word root
  flagStored : source.memory (m+8#64)=.word 0#64
  payload : TrieWalk.Payload source.memaddrs pointer size limit
  extra : property pointer size
  empty : property 0#64 0#64
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  values : TrieWalk.Values graph limit property
  regions : graph.Regions cutoff heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions cutoff heap.toNat
  separated : graph.PathSeparated

/-- Actual post-conversion operands and graph, ready for the original
root load and insertion. The converted query has an owned current lifetime. -/
structure Converted (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m pointer size : BitVec 64) (cutoff limit : Nat)
    (property : BitVec 64→BitVec 64→Prop := fun _ _=>True) where
  root : BitVec 64
  heap : BitVec 64
  key : BitVec 64
  length : BitVec 64
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)])
  pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer))
  sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))
  small : length.toNat≤64
  pointerActive : pointer≠0#64
  sizeActive : size≠0#64
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  installed : Input.OriginalCode.Installed source.code
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  heapUpper : heap.toNat≤2952790016
  headerArena : AllocatedBytes.Arena m 16
  headerAligned : m.toNat%8=0
  headerBefore : m.toNat+16≤cutoff
  cutoffAligned : cutoff%8=0
  floor : cutoff≤heap.toNat
  rootStored : source.memory m=.word root
  flagStored : source.memory (m+8#64)=.word 0#64
  payload : TrieWalk.Payload source.memaddrs pointer size limit
  extra : property pointer size
  empty : property 0#64 0#64
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  values : TrieWalk.Values graph limit property
  regions : graph.Regions cutoff heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions cutoff heap.toNat
  separated : graph.PathSeparated
  query : graph.PathBuffer source.be cutoff heap.toNat key length.toNat

/-- The actual normal key call supplies this conversion contract; neither
its allocation nor the later mutation is assumed to succeed. -/
theorem Entry.after_key {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {m rawKey pointer size : BitVec 64} {byteLength cutoff limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (entry : Entry source m rawKey byteLength pointer size cutoff limit property)
    (reached : Input.CallPrefix.Reaches source (.scoped (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments) target) :
    Nonempty (Converted target m pointer size cutoff limit property) := by
  have mapped : source.memaddrs (m+8#64):=by
    simpa only [byteAddress] using AllocatedBytes.word_mapped source m 16 8 entry.domain entry.headerArena (by decide) entry.headerAligned (by decide)
  obtain ⟨arena,nk,saved,view,price,frame,memory⟩:=NibbleKey.scoped_normal (ofString "nk") SetTrie.keyArguments m rawKey entry.heap byteLength
    entry.small entry.installed entry.domain entry.little (SetTrie.key_arguments source m rawKey byteLength entry.mCell entry.keyCell entry.lengthCell)
    mapped entry.flagStored entry.heapCell entry.heapArena entry.heapAligned entry.inputArena entry.inputBefore reached
  have countBound : 2*byteLength≤64:=by have small:=entry.small; omega
  have lengthNumber : (BitVec.ofNat 64 (2*byteLength)).toNat=2*byteLength:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨heapCell,nextArena,aligned,grows,globals,fields,next,same,regions,disjoint,⟨values⟩,paths,pathRegions,separated,query⟩:=
    NibbleKey.graph_after_unsecured_query source target entry.heap (2*byteLength) countBound entry.graph limit cutoff cutoff property
      entry.values entry.regions entry.disjoint entry.paths entry.pathRegions entry.separated entry.floor arena entry.heapAligned view frame
      (fun address before=>memory address (Or.inl before))
  have domainEq:=Input.MemoryMetadata.domain frame
  change target.memaddrs=source.memaddrs at domainEq
  have endianEq:=Input.MemoryMetadata.endian frame
  change target.be=source.be at endianEq
  have codeEq:=Input.MemoryMetadata.code frame
  change target.code=source.code at codeEq
  have flagNumber : (m+8#64).toNat=m.toNat+8:=byteAddress_toNat m 8 (by have upper:=entry.headerArena.upper; omega)
  refine ⟨{
    root:=entry.root,heap:=PersistentAlloc.rounded entry.heap (BitVec.ofNat 64 (2*byteLength)),key:=entry.heap,length:=BitVec.ofNat 64 (2*byteLength)
    mCell:=(saved _ (by decide)).trans entry.mCell
    nkCell:=nk
    pointerCell:=(saved _ (by decide)).trans entry.pointerCell
    sizeCell:=(saved _ (by decide)).trans entry.sizeCell
    small:=by rw [lengthNumber]; exact countBound
    pointerActive:=entry.pointerActive,sizeActive:=entry.sizeActive
    domain:=domainEq.trans entry.domain,little:=endianEq.trans entry.little
    installed:=by rw [codeEq]; exact entry.installed
    heapCell:=heapCell,heapArena:=nextArena,heapAligned:=aligned
    heapUpper:=NibbleKey.scoped_heap_upper (ofString "nk") SetTrie.keyArguments m rawKey entry.heap byteLength
      entry.small entry.installed (SetTrie.key_arguments source m rawKey byteLength entry.mCell entry.keyCell entry.lengthCell)
      mapped entry.flagStored entry.heapCell entry.heapArena reached
    headerArena:=entry.headerArena,headerAligned:=entry.headerAligned,headerBefore:=entry.headerBefore,cutoffAligned:=entry.cutoffAligned
    floor:=Nat.le_trans entry.floor grows
    rootStored:=(memory m (Or.inl (by have bound:=entry.headerBefore; have before:=entry.floor; omega))).trans entry.rootStored
    flagStored:=(memory (m+8#64) (Or.inl (by rw [flagNumber]; have bound:=entry.headerBefore; have before:=entry.floor; omega))).trans entry.flagStored
    payload:=by rw [domainEq]; exact entry.payload
    extra:=entry.extra,empty:=entry.empty
    graph:=next,member:=by rw [same]; exact entry.member
    values:=values,regions:=regions,disjoint:=disjoint,paths:=paths,pathRegions:=pathRegions,separated:=separated
    query:=by rw [lengthNumber]; exact query }⟩

end InitECandidate.Solver.Mpt.IndexedSet

#print axioms InitECandidate.Solver.Mpt.IndexedSet.Entry.after_key
