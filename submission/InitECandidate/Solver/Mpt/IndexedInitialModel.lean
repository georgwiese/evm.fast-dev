import InitECandidate.Solver.Mpt.IndexedKeyBuffer
import InitECandidate.Solver.Mpt.IndexedLoopNormal
import InitECandidate.Solver.Mpt.NewProtected

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual reached heap-mark/new-map/i=0 setup supplies the full
initial loop model. Its registry starts empty and its original slice
array stays below the marked allocation frontier. -/
theorem initial_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap array : BitVec 64)
    (count limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (room : AllocatedBytes.Arena heap 16) (aligned : heap.toNat%8=0) (heapLower : 2713731432≤heap.toNat)
    (countBound : count<2^64) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (installed : Input.OriginalCode.Installed source.code) (bindings : Input.Main.MptWorkspace.Bindings source)
    (hash : Keccak256.Environment source 2713714976#64 2713715176#64)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (rows : SliceArray source array count heap.toNat limit slices property) (empty : property 0#64 0#64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array))) :
    ∃ model : LoopModel (loopEntry source heap) heap array count heap.toNat limit slices property,model.index=0#64 := by
  let markedSource:=marked source heap
  let old:=TrieWalk.Graph.empty markedSource.memory markedSource.memaddrs
  obtain ⟨_fields,graph,_same,regions,disjoint,⟨values⟩,paths,pathRegions,separated,header⟩:=NewTrie.post_graph markedSource heap 0#64 0#64 room aligned old limit heap.toNat heap.toNat property
    (TrieWalk.Values.empty _ _ limit property) (TrieWalk.Graph.Regions.empty _ _ _ _) (TrieWalk.Graph.Disjoint.empty _ _)
    (TrieWalk.Graph.PathBytes.empty _ _ _) (TrieWalk.Graph.PathRegions.empty _ _ _ _) (TrieWalk.Graph.PathSeparated.empty _ _) old.null
  let current:=loopEntry source heap
  have heapFacts:=loop_entry_heap source heap room
  have globals:=loop_entry_globals source heap
  have cells:=loop_entry_locals source heap
  have currentRows:=rows.of_band source current array count heap.toNat limit slices property rfl (by
    intro query _above before
    exact loop_entry_older source heap query room before)
  have currentScratch : Rlp.Validation.Arena current 2713714688#64 2701135872#64:={
    domain:=scratch.domain
    cursorGlobal:=(globals _ (by decide)).trans scratch.cursorGlobal
    limitGlobal:=(globals _ (by decide)).trans scratch.limitGlobal
    ordered:=scratch.ordered
    aligned:=scratch.aligned
    lower:=scratch.lower
    upper:=scratch.upper }
  let model : LoopModel current heap array count heap.toNat limit slices property:={
    index:=0#64
    root:=0#64
    heap:=PersistentAlloc.rounded heap 16#64
    indexCell:=cells.2
    countCell:=(loop_entry_saved source heap (ofString "n") (by decide) (by decide) (by decide)).trans countCell
    mCell:=cells.1
    arrayCell:=(loop_entry_saved source heap (ofString "slice_arr") (by decide) (by decide) (by decide)).trans arrayCell
    bounded:=Nat.zero_le _
    countBound:=countBound
    cutoffLower:=heapLower
    cutoffAligned:=aligned
    floor:=by have grows:=heapFacts.2.2.2; omega
    headerAbove:=Nat.le_refl _
    headerBefore:=heapFacts.2.2.2
    domain:=domain
    little:=little
    installed:=installed
    bindings:=loop_entry_bindings source heap bindings
    hash:=hash.of_fields source current 2713714976#64 2713715176#64 rfl rfl rfl globals
    scratch:=currentScratch
    heapCell:=heapFacts.1
    heapArena:=heapFacts.2.1
    heapAligned:=heapFacts.2.2.1
    rows:=currentRows
    graph:=graph
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    header:=header.of_erase (NewTrie.post markedSource heap 0#64 0#64) current graph graph heap 0#64 0#64 rfl rfl
    empty:=empty }
  exact ⟨model,rfl⟩

/-- A genuine normal whole-builder run establishes its own initial live
model and actual loop continuation. No successful future allocation or
future physical graph is a premise of this entry connection. -/
theorem normal_loop_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap array : BitVec 64)
    (count limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (heapLower : 2713731432≤heap.toNat)
    (countBound : count<2^64) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (installed : Input.OriginalCode.Installed source.code) (bindings : Input.Main.MptWorkspace.Bindings source)
    (hash : Keccak256.Environment source 2713714976#64 2713715176#64)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (rows : SliceArray source array count heap.toNat limit slices property) (empty : property 0#64 0#64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ (inner : PanSemStateFiniteExact 64 Guest.HostMemory) (model : LoopModel (loopEntry source heap) heap array count heap.toNat limit slices property),
      model.index=0#64 ∧ target.clock=inner.clock ∧ evaluateHOLFiniteState (loopEntry source heap) loopAndAfter=(some (.returned value),inner) := by
  obtain ⟨room,inner,clock,continued⟩:=normal_setup source target heap installed heapCell domain frontier aligned value normal
  obtain ⟨model,index⟩:=initial_model source heap array count limit slices property room aligned heapLower countBound domain little installed bindings hash scratch rows empty countCell arrayCell
  exact ⟨inner,model,index,clock,continued⟩

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.initial_model
#print axioms InitECandidate.Solver.Mpt.Indexed.normal_loop_entry
