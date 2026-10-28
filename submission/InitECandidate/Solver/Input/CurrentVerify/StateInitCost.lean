import InitECandidate.Solver.Input.CurrentVerify.StateInputs
import InitECandidate.Solver.Input.CurrentVerify.StateWorkspace
import InitECandidate.Solver.Input.CurrentVerify.WitnessRootCost
import InitECandidate.Solver.Mpt.CurrentStateInitSuffixCost

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem state_root_call_price {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap root heap : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word table)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source Mpt.StateInit.rootCall).2.clock≤200623 := by
  obtain ⟨callee,called,dbLocal,rootLocal⟩:=word_pair_environment source.code.lookup (ofString "decode_witness_to_mpt")
    (ofString "db") (ofString "root_hash") Mpt.WitnessDecodeRoot.body .one table root (by decide)
    (Mpt.WitnessDecodeRoot.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.StateInit.rootArguments=
      some [.val (.word table),.val (.word root)] := by
    simp [Mpt.StateInit.rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,nodesCell,rootCell]
  have entryWitness : CurrentStartup.WitnessArrays.Image input (callEntryStateHOLFinite source callee) pointer si array start length boundary 40 1024 (2^31) :=
    witness.of_interval (by decide) (by intros; rfl)
  have entryImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} (callEntryStateHOLFinite source callee) (VarList.decodedCount input start length) :=
    tableImage.of_interval rfl rfl (by intros; rfl)
  have bodyPrice:=witness_root_price entryWitness entryImage dbLocal rootLocal before heapCell heapArena heapBound aligned (arena.of_frame rfl)
  rw [Mpt.StateInit.shapes.2.2.2.2]
  exact ClockCost.scoped_reached_current source "root" .one (ofString "decode_witness_to_mpt") Mpt.StateInit.rootArguments _
    Mpt.WitnessDecodeRoot.body Mpt.StateInit.afterRoot callee .one 200544 78 args called bodyPrice (by
      intro target value normal checked
      have codeEq:=(evaluation_fields (callEntryStateHOLFinite source callee) target Mpt.WitnessDecodeRoot.body _ normal).2.2.2
      exact Mpt.StateInit.current_after_root_price source.code arena.code (CallNormal.continuationEntry source target "root" value) codeEq)

/-- The complete unchanged current320 receives these entry conditions from
main's real databases and state_init call. Its workspace allocation derives
the room needed to protect those images before root decoding. -/
theorem state_init_price {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (inputs : StateInitInputs input source pointer si boundary) :
    source.clock-(evaluateHOLFiniteState source Mpt.StateInit.body).2.clock≤200624 := by
  obtain ⟨array,table,cap,root,codes,heap,start,length,arena,witness,image,heapCell,heapLower,heapUpper,aligned,inputBefore,tableBefore,nodesCell,rootCell,codesCell⟩:=inputs
  let output:=evaluateHOLFiniteState source Mpt.StateInit.body
  rcases Mpt.StateInit.root_trace source output.2 heap table root codes arena.code heapCell heapLower heapUpper aligned
      nodesCell rootCell codesCell arena.domain output.1 rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨room,funded,continued⟩:=entered
    let ready:=Mpt.StateInit.ready source heap table root codes
    let next:=PersistentAlloc.rounded heap 40#64
    have checked:=PersistentAlloc.guards heap 40#64 room
    have nextArena : AllocatedBytes.Arena next 0:=⟨by have grows:=checked.2.2.1; change heap.toNat+40≤next.toNat at grows; omega,
      by have upper:=checked.2.2.2.1; change next.toNat≤2952790016 at upper; omega⟩
    obtain ⟨readyArena,readyWitness,readyImage⟩:=state_workspace_node_image (root:=root) (codes:=codes) witness image arena room inputBefore tableBefore
    have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) := by
      simp [ready,Mpt.StateInit.ready,Mpt.StateInit.written,Mpt.StateInit.allocated,putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,next,
        show ofString "ws"≠ofString "heap_ptr" from by decide]
    have price:=state_root_call_price readyWitness readyImage nodesCell rootCell (by have grows:=checked.2.2.1; change heap.toNat+40≤next.toNat at grows; omega)
      nextHeap nextArena checked.2.2.2.1 checked.2.2.2.2 readyArena
    rw [continued] at price
    change source.clock-1-output.2.clock≤200623 at price
    change source.clock-output.2.clock≤200624
    omega

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_root_call_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.state_init_price
