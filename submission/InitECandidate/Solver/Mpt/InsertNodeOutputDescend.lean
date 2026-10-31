import InitECandidate.Solver.Mpt.InsertNodeOutput
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Package the five actual scalar descent updates. The registered graph
and current full query buffer are unchanged; progress comes from the real
branch or positive-extension descent proof. -/
theorem descend_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length level root child address nextLevel : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (rootMember : graph.valid root) (childMember : graph.valid child) (slot : graph.ParentSlot address)
    (positive : level.toNat<nextLevel.toNat) (bounded : nextLevel.toNat≤length.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (active : root≠0#64) (clean : TrieWalk.Uncached source.memory root)
    (nonhash : wordAt source.memory root≠0#64)
    (endpoint : target=QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "r" root)
      "next_node" child) "next_slot" address) "next_level" nextLevel) "go" 1#64) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  subst target
  exact ⟨{
    root:=root
    nextNode:=child
    nextSlot:=address
    nextLevel:=nextLevel
    go:=1#64
    heap:=heap
    rootCell:=by simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    nodeCell:=by simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    slotCell:=by simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    levelCell:=by simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    goCell:=by simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    stable:=by
      intro name notRoot notNode notSlot notLevel notGo
      simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notRoot,Ne.symm notNode,Ne.symm notSlot,Ne.symm notLevel,Ne.symm notGo]
    domain:=rfl
    endian:=rfl
    code:=rfl
    heapCell:=heapCell
    heapArena:=arena
    heapAligned:=aligned
    heapGrows:=Nat.le_refl _
    olderPrefix:=by intro query before; rfl
    oldPathFields:=⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
    cacheFrame:=TrieWalk.Graph.CacheFrame.refl graph
    rootUncached:=clean
    rootActive:=active
    rootNonHash:=nonhash
    protectedMemory:=by intro address safe before; rfl
    tags:=by intro node live active; rfl
    graph:=graph
    oldMember:=fun node live=>live
    freshMembers:=by intro node live; exact Or.inl live
    protectedGraph:=by intro address safe _before _away; exact safe
    activeRegistry:=by intro nonzero; rfl
    rootMember:=rootMember
    nodeMember:=childMember
    nextParent:=slot
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    step:=Or.inr ⟨rfl,positive,bounded⟩
    query:=by intro nonzero; exact buffer }⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.descend_output
