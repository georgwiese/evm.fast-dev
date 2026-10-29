import InitECandidate.Solver.Input.CurrentVerify.StateRootNormal
import InitECandidate.Solver.Mpt.CurrentStateInitAfterRootMemory

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Whole unchanged state_init320 normal execution retains every word before
its actual incoming heap, complete runtime metadata, restored scratch/frame
cursors and a genuinely advanced bounded/aligned heap. All helper allocation
room comes from the same observed execution and real main-derived inputs. -/
theorem state_init_normal_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (inputs : StateInitInputs input source pointer si boundary) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Mpt.StateInit.body=(some (.returned value),post)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post heap := by
  obtain ⟨array,table,cap,root,codes,heap,start,length,arena,witness,image,heapCell,heapLower,heapUpper,aligned,inputBefore,tableBefore,nodesCell,rootCell,codesCell⟩:=inputs
  obtain ⟨room,funded,continued⟩:=Mpt.StateInit.current_root_normal_trace source post heap table root codes arena.code heapCell heapLower heapUpper aligned
    nodesCell rootCell codesCell arena.domain value normal
  let ready:=Mpt.StateInit.ready source heap table root codes
  let next:=PersistentAlloc.rounded heap 40#64
  have checked:=PersistentAlloc.guards heap 40#64 room
  have nextArena : AllocatedBytes.Arena next 0:=
    ⟨by have grows:=checked.2.2.1; change heap.toNat+40≤next.toNat at grows; omega,
      by have upper:=checked.2.2.2.1; change next.toNat≤2952790016 at upper; omega⟩
  have grows : heap.toNat≤next.toNat:=by have bigger:=checked.2.2.1; change heap.toNat+40≤next.toNat at bigger; omega
  obtain ⟨readyArena,readyWitness,readyImage⟩:=state_workspace_node_image (root:=root) (codes:=codes) witness image arena room inputBefore tableBefore
  have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) := by
    simp [ready,Mpt.StateInit.ready,Mpt.StateInit.written,Mpt.StateInit.allocated,putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,next,
      show ofString "ws"≠ofString "heap_ptr" from by decide]
  have first : PersistentMemoryFrame source ready heap:=
    ⟨⟨next,nextHeap,nextArena,checked.2.2.2.1,checked.2.2.2.2,grows⟩,rfl,
      fun query before=>Mpt.StateInit.ready_memory_before source heap table root codes query room before⟩
  obtain ⟨target,node,inner,bounds,rootFrame,tailRun,endpoint⟩:=state_root_normal_trace readyWitness readyImage nodesCell rootCell
    (by omega) nextHeap nextArena checked.2.2.2.1 checked.2.2.2.2 readyArena value continued
  let called:=CallNormal.continuationEntry ready target "root" (.val (.word node))
  have wsCell : ready.globals.lookup (ofString "ws")=some (.val (.word heap)):=putGlobal.lookup_same _ _ _
  have context : Mpt.StateInit.WorkspaceContext called heap heap := by
    refine ⟨rootFrame.current_arena readyArena,?_,(rootFrame.globals _ (by decide)).trans wsCell,⟨Nat.le_refl _,heapUpper⟩⟩
    obtain ⟨last,cell,lastArena,lastBound,lastAligned,later⟩:=rootFrame.nextHeap
    exact ⟨last,cell,lastArena,lastBound,lastAligned,Nat.le_trans grows later⟩
  have nodeCell : called.locals.lookup (ofString "root")=some (.val (.word node)):=CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨valueEq,lastArena,lastFrame⟩:=Mpt.StateInit.MemorySuffix.after_root_memory called inner heap heap node context nodeCell value tailRun
  have throughRoot:=first.trans source ready called heap next rootFrame.memory_frame grows
  have total:=throughRoot.trans source called inner heap heap lastFrame (Nat.le_refl _)
  exact ⟨heap,heapCell,valueEq,(by rw [endpoint]; exact lastArena.of_frame rfl),
    total.of_erase source inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_init_normal_memory
