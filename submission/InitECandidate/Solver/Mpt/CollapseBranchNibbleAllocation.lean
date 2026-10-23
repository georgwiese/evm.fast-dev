import InitECandidate.Solver.Mpt.CollapseBranchNibbleStore
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def nibbleAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 8#64) "nib" heap

/-- The real original eight-byte allocation and selected-byte write
derive their actual protected buffer and continuation. No allocation-room
or future graph-success premise is supplied by the caller. -/
theorem nibble_entry_paths (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap index : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (lower : pathLower≤heap.toNat) (bounded : index.toNat<16)
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source nibbleScope=(some (.returned value),post)) :
    let nextHeap:=PersistentAlloc.rounded heap 8#64
    ∃ ready inner,ready.locals=source.locals.update (ofString "nib",.val (.word heap)) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧ source.clock-ready.clock≤1 ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧ AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧ heap.toNat+8≤nextHeap.toNat ∧
      evaluateHOLFiniteState ready afterStore=(some (.returned value),inner) ∧ post=restore source "nib" inner ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nextHeap.toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower nextHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower nextHeap.toNat heap 1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 8#64]=some (PersistentAlloc.values 8#64):=rfl
  rw [child_shapes.2.2.2.2.1] at normal
  obtain ⟨room,_funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal source post "nib" [.const 8#64] afterNibble heap 8#64 args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=frontier.upper; omega) value normal
  let nextHeap:=PersistentAlloc.rounded heap 8#64
  have guards:=PersistentAlloc.guards heap 8#64 room
  have grows : heap.toNat+8≤nextHeap.toNat:=guards.2.2.1
  have allocatedArena : AllocatedBytes.Arena heap 8:=⟨frontier.lower,room⟩
  have nextArena : AllocatedBytes.Arena nextHeap 0:=⟨by have lower:=frontier.lower; omega,guards.2.2.2.1⟩
  let allocated:=nibbleAllocated source heap
  have currentNibble : allocated.locals.lookup (ofString "nib")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have currentIndex : allocated.locals.lookup (ofString "idx")=some (.val (.word index)):=
    (bind_lookup_other _ "nib" "idx" heap (by decide)).trans indexCell
  obtain ⟨storeRun,older,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffer⟩:=
    nibble_store_paths allocated heap index nextHeap graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated lower grows allocatedArena aligned bounded
      currentNibble currentIndex little domain
  let ready:=nibblePost allocated heap index
  change evaluateHOLFiniteState allocated afterNibble=(some (.returned value),inner) at continued
  rw [child_shapes.2.2.2.2.2.1,StateSteps.next_sequence allocated ready nibbleStore afterStore storeRun (Nat.le_refl _)] at continued
  have finalHeapCell : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)):=by
    simp [ready,nibblePost,allocated,nibbleAllocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,nextHeap]
  exact ⟨ready,inner,rfl,rfl,rfl,rfl,(by change source.clock-(source.clock-1)≤1; omega),finalHeapCell,nextArena,guards.2.2.2.2,grows,continued,endpoint,older,
    next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffer⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.nibble_entry_paths
