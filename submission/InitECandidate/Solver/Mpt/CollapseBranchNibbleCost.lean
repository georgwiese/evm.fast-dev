import InitECandidate.Solver.Mpt.CollapseBranchNibbleAllocation
import InitECandidate.Solver.Mpt.CollapseBranchAfterStoreCost
import InitECandidate.Solver.WitnessRadix.AllocationTrace

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All original nib-scope outcomes. A stopped allocation fits the small
guard allowance; only its real normal return supplies destination room and
the exact state for the byte store and suffix. No future graph is assumed. -/
theorem nibble_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap index child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower) (bounded : index.toNat<16)
    (member : graph.valid child) (active : child≠0#64) (notHash : wordAt source.memory child≠0#64)
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source nibbleScope).2.clock≤afterStorePrice source.memory child+1 := by
  let output:=evaluateHOLFiniteState source nibbleScope
  have actual : evaluateHOLFiniteState source (.decCall (ofString "nib") .one (ofString "alloc") [.const 8#64] afterNibble)=(output.1,output.2):=by rw [←child_shapes.2.2.2.2.1]
  have minimum:=after_store_price_lower source.memory child
  rcases PersistentAlloc.scoped_trace source output.2 "nib" [.const 8#64] afterNibble heap 8#64 rfl installed heapCell (by have upper:=frontier.upper; omega) output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤_
    omega
  · obtain ⟨_funded,room,inner,continued,endpoint⟩:=reached
    let nextHeap:=PersistentAlloc.rounded heap 8#64
    let allocated:=nibbleAllocated source heap
    let ready:=nibblePost allocated heap index
    have guards:=PersistentAlloc.guards heap 8#64 room
    have grows : heap.toNat+8≤nextHeap.toNat:=guards.2.2.1
    have arena : AllocatedBytes.Arena heap 8:=⟨frontier.lower,room⟩
    have nextArena : AllocatedBytes.Arena nextHeap 0:=⟨by have lower:=frontier.lower; omega,guards.2.2.2.1⟩
    have allocatedNibble : allocated.locals.lookup (ofString "nib")=some (.val (.word heap)):=bind_lookup_same _ _ _
    have allocatedIndex : allocated.locals.lookup (ofString "idx")=some (.val (.word index)):=
      (bind_lookup_other _ "nib" "idx" heap (by decide)).trans indexCell
    obtain ⟨storeRun,older,current,same,_currentRegions,_currentDisjoint,_currentValues,_currentPaths,currentPathRegions,_currentSeparated,buffer⟩:=
      nibble_store_paths allocated heap index nextHeap graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated lower grows arena aligned bounded allocatedNibble allocatedIndex little domain
    have childBefore : child.toNat<heap.toNat:=by
      have before:=(regions child member active).2.2.2
      have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory child)
      omega
    have inside : 40<TrieWalk.nodeBytes (wordAt source.memory child):=by
      rcases (graph.kind_cases child member active).resolve_left notHash with one|two|three
      · rw [one]; decide
      · rw [two]; decide
      · rw [three]; decide
    have fieldBefore : (child+40#64).toNat<heap.toNat:=by
      simpa only [byteAddress] using (graph.region_query_bounds nodeLower heap.toNat regions child 40 member active inside).2
    have currentTag : wordAt ready.memory child=wordAt source.memory child:=congrArg MemoryBytes.wordBits (older child childBefore)
    have currentLength : wordAt ready.memory (child+40#64)=wordAt source.memory (child+40#64):=congrArg MemoryBytes.wordBits (older _ fieldBefore)
    have currentChild : ready.locals.lookup (ofString "child")=some (.val (.word child)):=
      (bind_lookup_other _ "nib" "child" heap (by decide)).trans childCell
    have currentKind : ready.locals.lookup (ofString "ck")=some (.val (.word (wordAt ready.memory child))):=by
      rw [currentTag]
      exact (bind_lookup_other _ "nib" "ck" heap (by decide)).trans tagCell
    have currentMember : current.valid child:=by rw [same]; exact member
    have currentNotHash : wordAt ready.memory child≠0#64:=by rwa [currentTag]
    have currentHeapCell : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)):=by
      simp [ready,nibblePost,allocated,nibbleAllocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,nextHeap]
    have price:=after_store_cost ready nextHeap heap child current pathLower currentPathRegions buffer floor currentMember active currentNotHash allocatedNibble currentChild currentKind currentHeapCell
      nextArena domain installed
    have samePrice : afterStorePrice ready.memory child=afterStorePrice source.memory child:=by simp only [afterStorePrice,currentTag,currentLength]
    rw [samePrice] at price
    have suffixCost : allocated.clock-(evaluateHOLFiniteState allocated afterNibble).2.clock≤afterStorePrice source.memory child:=by
      rw [child_shapes.2.2.2.2.2.1,StateSteps.next_sequence allocated ready nibbleStore afterStore storeRun (Nat.le_refl _)]
      exact price
    change evaluateHOLFiniteState allocated afterNibble=(output.1,inner) at continued
    rw [continued] at suffixCost
    change source.clock-1-inner.clock≤afterStorePrice source.memory child at suffixCost
    have endpointClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤_
    rw [endpointClock]
    omega

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.nibble_cost
