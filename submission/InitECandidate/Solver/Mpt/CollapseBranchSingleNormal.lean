import InitECandidate.Solver.Mpt.CollapseBranchChildEntry
import InitECandidate.Solver.Mpt.CollapseBranchNibbleNormal

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole real single-child scope. The original scan's saved slot selects
the registered nonnull child; actual child/ck guards, nib allocation/store,
merge/constructor and both lexical restorations derive the final model. -/
theorem single_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node index : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index))) (bounded : index.toNat<16)
    (selectedNonzero : wordAt source.memory (node+32#64+index*8#64)≠0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source childScope=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ child root finalHeap : BitVec 64,graph.valid child ∧ child≠0#64 ∧ wordAt source.memory child≠0#64 ∧
        source.clock-target.clock≤afterStorePrice source.memory child+1 ∧ value=.val (.word root) ∧
        target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧ AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧
        heap.toNat≤root.toNat ∧ root.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → next.ProtectedWord address) := by
  obtain ⟨child,inner,childMember,childActive,continued,endpoint⟩:=child_entry_normal source target node index graph member active tag nodeCell indexCell bounded selectedNonzero value normal
  let selected:=QueryBranch.bind source "child" child
  let entered:=QueryBranch.bind selected "ck" (wordAt source.memory child)
  have currentIndex : entered.locals.lookup (ofString "idx")=some (.val (.word index)):=
    (bind_lookup_other selected "ck" "idx" _ (by decide)).trans ((bind_lookup_other source "child" "idx" child (by decide)).trans indexCell)
  have currentChild : entered.locals.lookup (ofString "child")=some (.val (.word child)):=
    (bind_lookup_other selected "ck" "child" _ (by decide)).trans (bind_lookup_same source "child" child)
  have currentTag : entered.locals.lookup (ofString "ck")=some (.val (.word (wordAt entered.memory child))):=bind_lookup_same _ _ _
  obtain ⟨notHash,nibbleRun⟩:=after_kind_entry entered inner (wordAt source.memory child) currentTag installed value continued
  obtain ⟨domainEq,endianEq,codeEq,price,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,fresh,grows,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,protection⟩:=
    nibble_paths entered inner heap index child graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated lower floor nodeFloor bounded childMember childActive notHash
      currentIndex currentChild currentTag heapCell frontier aligned little domain installed value nibbleRun
  rw [endpoint]
  exact ⟨domainEq,endianEq,codeEq,older,child,root,finalHeap,childMember,childActive,notHash,price,answer,finalCell,finalArena,finalAligned,fresh,grows,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,protection⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.single_paths
