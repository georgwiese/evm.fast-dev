import InitECandidate.Solver.Input.CurrentVerify.StateInputs
import InitECandidate.Solver.Mpt.StateInitPrefixFrame
import InitECandidate.Solver.Input.CurrentVerify.WitnessRootCost
import InitECandidate.Solver.Mpt.CurrentStateInitSuffixCost

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem state_root_call_price (data : CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root heap : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source Mpt.StateInit.rootCall).2.clock≤1757412483564 := by
  obtain ⟨callee,called,dbLocal,rootLocal⟩:=word_pair_environment source.code.lookup (ofString "decode_witness_to_mpt")
    (ofString "db") (ofString "root_hash") Mpt.WitnessDecodeRoot.body .one data.table root (by decide)
    (Mpt.WitnessDecodeRoot.original_code source.code live.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.StateInit.rootArguments=
      some [.val (.word data.table),.val (.word root)] := by
    simp [Mpt.StateInit.rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,nodesCell,rootCell]
  let entry:=callEntryStateHOLFinite source callee
  have bodyPrice:=witness_root_price data entry root heap (database.of_frame rfl) tableBefore dbLocal rootLocal heapCell heapArena heapBound aligned (live.of_frame rfl)
  rw [Mpt.StateInit.shapes.2.2.2.2]
  have whole:=ClockCost.scoped_reached_current source "root" .one (ofString "decode_witness_to_mpt") Mpt.StateInit.rootArguments _
    Mpt.WitnessDecodeRoot.body Mpt.StateInit.afterRoot callee .one 1757412483485 78 args called bodyPrice (by
      intro target value normal checked
      have codeEq:=(evaluation_fields entry target Mpt.WitnessDecodeRoot.body _ normal).2.2.2
      exact Mpt.StateInit.current_after_root_price source.code live.code (CallNormal.continuationEntry source target "root" value) codeEq)
  exact whole.trans (by omega)

/-- The complete unchanged current320 receives these entry conditions from
main's real databases and state_init call. Its workspace allocation derives
the room needed to protect those images before root decoding. -/
theorem state_init_price {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (inputs : StateInitInputs input source pointer si boundary) :
    source.clock-(evaluateHOLFiniteState source Mpt.StateInit.body).2.clock≤1757412483565 := by
  obtain ⟨array,table,cap,root,codes,heap,start,length,arena,witness,image,heapCell,heapLower,heapUpper,aligned,inputBefore,tableBefore,nodesCell,rootCell,codesCell,nodeData,database,actualTable,actualTableBefore⟩:=inputs
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
    have readyArena:=Mpt.StateInit.ready_arena source heap table root codes arena
    have readyDatabase : CurrentTable.NodeLookup.Database ready nodeData:=database.of_before heap.toNat actualTableBefore rfl rfl
      (fun query earlier=>Mpt.StateInit.ready_memory_before source heap table root codes query room earlier)
    have actualNodes : ready.locals.lookup (ofString "nodedb")=some (.val (.word nodeData.table)):=by
      rw [actualTable]
      exact nodesCell
    have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) := by
      simp [ready,Mpt.StateInit.ready,Mpt.StateInit.written,Mpt.StateInit.allocated,putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,next,
        show ofString "ws"≠ofString "heap_ptr" from by decide]
    have nextBefore : (CurrentTable.New.endPointer nodeData.table nodeData.cap).toNat≤next.toNat:=
      actualTableBefore.trans (by have grows:=checked.2.2.1; change heap.toNat+40≤next.toNat at grows; omega)
    have price:=state_root_call_price nodeData ready root next readyDatabase nextBefore actualNodes rootCell
      nextHeap nextArena checked.2.2.2.1 checked.2.2.2.2 (Rlp.LiveArena.of_startup readyArena)
    rw [continued] at price
    change source.clock-1-output.2.clock≤1757412483564 at price
    change source.clock-output.2.clock≤1757412483565
    omega

/-- Main's actual header/gas/database/state-init prefix either stops within
this allowance or reaches the real continuation after a checked state_init
return. The root read and every materializer entry are derived, not assumed. -/
theorem RunAttempt.through_state_init {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤1760801932784 ∨ ∃ caller entry target value inner,
      RunAttempt.HasTables input caller pointer si record gasWord boundary ∧
      StateInitInputs input entry pointer si boundary ∧
      evaluateHOLFiniteState entry Mpt.StateInit.body=(some (.returned value),target) ∧
      shapeEqHOL (shapeOfHOLExact value) .one=true ∧
      source.clock-target.clock≤1760801932784 ∧
      evaluateHOLFiniteState {target with locals:=caller.locals} RunAttempt.afterStateInit=(outcome,inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rcases RunAttempt.to_state_init data outcome run with stopped|reached
  · exact Or.inl (stopped.trans (by omega))
  · obtain ⟨caller,inner,tables,callerForward,prefixPrice,continued,postClock,postFrame⟩:=reached
    rcases RunAttempt.state_init_entry_trace tables outcome continued with stopped|entered
    · exact Or.inl (by rw [postClock]; omega)
    · obtain ⟨entry,target,childResult,inputs,entryFrame,entryClock,bodyRun,resumes⟩:=entered
      have paid:=state_init_price inputs
      rw [bodyRun] at paid
      change entry.clock-target.clock≤1757412483565 at paid
      have bodyForward:=evaluateHOLFiniteState_clock_le entry Mpt.StateInit.body
      rw [bodyRun] at bodyForward
      change target.clock≤entry.clock at bodyForward
      have total : source.clock-target.clock≤1760801932784:=by omega
      rcases resumes with halted|normal
      · exact Or.inl (by rw [postClock,halted]; exact total)
      · obtain ⟨value,returned,checked,afterRun⟩:=normal
        rw [returned] at bodyRun
        exact Or.inr ⟨caller,entry,target,value,inner,tables,inputs,bodyRun,checked,total,afterRun,postClock,postFrame⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_root_call_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.state_init_price

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.through_state_init
