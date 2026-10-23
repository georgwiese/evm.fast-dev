import InitECandidate.Solver.Mpt.DeleteExtensionConcat
import InitECandidate.Solver.Mpt.DeleteExtensionConstructor

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole genuine concatenating deletion finish. The real cat allocation,
cl declaration and original constructor tail call derive the new root,
current heap and complete retained registry. Every older word survives. -/
theorem merge_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (nodeFloor : nodeLower≤heap.toNat) (positive : 0<length.toNat)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source concatScope=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+22 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,graph.valid node → next.valid node) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  obtain ⟨ready,inner,localsEq,readyDomain,readyEndian,readyCode,copyPrice,continued,endpoint,nextHeapCell,nextArena,nextAligned,grows,older,
    current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,buffer⟩:=
    concat_entry source target heap child segment length graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated segmentBuffer floor
      member active tag segmentCell lengthCell childCell heapCell frontier aligned little domain installed value normal
  let childLength:=wordAt source.memory (child+40#64)
  let nextHeap:=PersistentAlloc.rounded heap (length+childLength)
  let total:=length+childLength
  change heap.toNat+length.toNat+childLength.toNat≤nextHeap.toNat at grows
  change source.clock-ready.clock≤length.toNat/8+childLength.toNat/8+19 at copyPrice
  have amount : total.toNat=length.toNat+childLength.toNat:=BitVec.toNat_add_of_lt (by
    have fits:=buffer.span.fits
    change heap.toNat+(length.toNat+childLength.toNat)<2^64 at fits
    omega)
  have positiveTotal : 0<total.toNat:=by rw [amount]; omega
  have childBefore : child.toNat<heap.toNat:=by
    have before:=(regions child member active).2.2.2
    have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory child)
    omega
  have fieldBefore : (child+40#64).toNat<heap.toNat:=by
    have inside : 40<TrieWalk.nodeBytes (wordAt source.memory child):=by rcases tag with tag|tag <;> rw [tag] <;> decide
    simpa only [byteAddress] using (graph.region_query_bounds nodeLower heap.toNat regions child 40 member active inside).2
  have currentTag : wordAt ready.memory child=wordAt source.memory child:=congrArg MemoryBytes.wordBits (older child childBefore)
  let oldPath:=graph.path child member active tag
  have oldStored : source.memory (child+40#64)=.word childLength:=by simp only [childLength,wordAt,oldPath.sizeStored,MemoryBytes.wordBits]
  have currentStored : ready.memory (child+40#64)=.word childLength:=(older _ fieldBefore).trans oldStored
  have mapped : ready.memaddrs (child+40#64):=by rw [readyDomain]; exact oldPath.sizeMapped
  have readyLength : ready.locals.lookup (ofString "sl")=some (.val (.word length)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "cat"≠ofString "sl" from by decide] using lengthCell
  have readyChild : ready.locals.lookup (ofString "nc")=some (.val (.word child)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "cat"≠ofString "nc" from by decide] using childCell
  have readyKey : ready.locals.lookup (ofString "cat")=some (.val (.word heap)):=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
  have readyTag : ready.locals.lookup (ofString "ck")=some (.val (.word (wordAt ready.memory child))):=by
    rw [localsEq,currentTag]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "cat"≠ofString "ck" from by decide] using tagCell
  have read : eval ready lengthExpression=some (.val (.word total)):=by
    simp [eval,lengthExpression,field,localVar,evalHOLExact,evalListHOLExact,toExact,readyLength,readyChild,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,currentStored,total]
  rw [merge_shapes.2.2.2.1] at continued
  obtain ⟨tail,tailRun,innerEq⟩:=Input.declaration_return_word ready inner "cl" lengthExpression total afterLength value read continued
  let made:=QueryBranch.bind ready "cl" total
  have madeKey : made.locals.lookup (ofString "cat")=some (.val (.word heap)):=
    (bind_lookup_other ready "cl" "cat" total (by decide)).trans readyKey
  have madeLength : made.locals.lookup (ofString "cl")=some (.val (.word total)):=bind_lookup_same _ _ _
  have madeChild : made.locals.lookup (ofString "nc")=some (.val (.word child)):=
    (bind_lookup_other ready "cl" "nc" total (by decide)).trans readyChild
  have madeTag : made.locals.lookup (ofString "ck")=some (.val (.word (wordAt made.memory child))):=
    (bind_lookup_other ready "cl" "ck" total (by decide)).trans readyTag
  have currentMember : current.valid child:=by rw [same]; exact member
  have pathTag : wordAt made.memory child=1#64 ∨ wordAt made.memory child=2#64:=by change wordAt ready.memory child=1#64 ∨ wordAt ready.memory child=2#64; rw [currentTag]; exact tag
  have madeBuffer : current.PathBuffer made.be pathLower nextHeap.toNat heap total.toNat:=by rw [amount]; exact buffer
  have madeInstalled : Input.OriginalCode.Installed made.code:=by change Input.OriginalCode.Installed ready.code; rw [readyCode]; exact installed
  obtain ⟨answer,tailDomain,tailEndian,tailCode,price,tailMemory,finalHeap,finalCell,finalArena,finalAligned,heapGrows,
    next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    constructor_paths made tail nextHeap child heap total current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated
      madeBuffer positiveTotal (by omega) currentMember active pathTag madeKey madeLength madeChild madeTag nextHeapCell nextArena nextAligned (readyDomain.trans domain) madeInstalled value tailRun
  rw [endpoint,innerEq]
  have finalPrice : source.clock-tail.clock≤length.toNat/8+childLength.toNat/8+22:=by
    change ready.clock-tail.clock≤3 at price
    omega
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : tail.memory query=source.memory query:=
    (tailMemory query (by omega)).trans (older query before)
  have included (node : BitVec 64) (old : graph.valid node) : next.valid node:=
    (members node).2 (Or.inl (by rw [same]; exact old))
  exact ⟨tailDomain.trans readyDomain,tailEndian.trans readyEndian,tailCode.trans readyCode,finalPrice,memory,
    nextHeap,finalHeap,answer,finalCell,finalArena,finalAligned,by omega,next,included,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.merge_paths
