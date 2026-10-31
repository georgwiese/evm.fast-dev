import InitECandidate.Solver.Input.CurrentVerify.WitnessRootLookup
import InitECandidate.Solver.Mpt.WitnessMaterializeBodyCost
import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost
import InitECandidate.Solver.Mpt.FailGuard

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch Mpt.WitnessDecodeRoot

/-- The real materializer receives the bounded row returned by the actual
Patricia lookup. Its complete ranked body and unconditional cache suffix
are priced on every outcome, including failed reads and allocations. -/
theorem witness_materialize_call_price (data : CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap root : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some (CurrentTable.NodeLookup.presentValue pointer length))
    (small : length.toNat≤1024) (lower : 2701131776≤pointer.toNat)
    (before : pointer.toNat+length.toNat≤data.table.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source materializeCall).2.clock≤1757412483215 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) materializeArguments=
      some [.val (.word data.table),.val (.word pointer),.val (.word length)] := by
    simp [materializeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,recordCell,CurrentTable.NodeLookup.presentValue]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup
    (ofString "_decode_witness_node") (ofString "db") (ofString "p") (ofString "n") Mpt.WitnessMaterialize.body .one
    data.table pointer length (by decide) (by decide) (by decide) (Mpt.WitnessMaterialize.original_code source.code live.code)
  obtain ⟨cursor,limit,physical,limitBound,cursorBound⟩:=live.cursors
  let entry:=callEntryStateHOLFinite source callee
  have bodyPrice:=Main.RunAttemptConstructors.materialize_body_cost data entry data.table pointer length heap cursor limit
    (database.of_frame rfl) tableBefore rfl dbLocal pointerLocal lengthLocal heapCell heapArena heapBound aligned heapArena.lower
    (live.of_frame rfl) (physical.of_fields source entry cursor limit rfl rfl) before small lower live.code
  rw [Main.RunAttemptConstructors.materialize_body_cost_value] at bodyPrice
  rw [lookup_tail_shape.2]
  have whole:=ClockCost.scoped_reached_current source "nd" .one (ofString "_decode_witness_node") materializeArguments _
    Mpt.WitnessMaterialize.body afterMaterialize callee .one 1757412483170 44 args called bodyPrice (by
      intro target value normal checked
      let ready:=CallNormal.continuationEntry source target "nd" value
      have currentRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
        (CallNormal.continuation_lookup_other source target "nd" "root_hash" value (by decide)).trans rootCell
      have codeEq:=(evaluation_fields entry target Mpt.WitnessMaterialize.body _ normal).2.2.2
      have installed : OriginalCode.Installed ready.code:=by change OriginalCode.Installed target.code; rw [codeEq]; exact live.code
      exact suffix_cost ready root installed currentRoot)
  exact whole.trans (by omega)

/-- The actual absent result executes the failure guard. A present result
supplies its own <=1024byte ordinary input before the built database. -/
theorem witness_after_lookup_price (data : CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root heap : BitVec 64) (answer : ValueHOL 64)
    (database : CurrentTable.NodeLookup.Database source data) (result : CurrentTable.NodeLookup.Result data answer)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some answer)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source afterLookup).2.clock≤1757412483215 := by
  rcases database.result result with absent|⟨pointer,length,present,allocated,small,lower,before⟩
  · rw [absent] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=evaluateHOLFiniteState source missingCall := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have stops : (evaluateHOLFiniteState source missingGuard).1≠none:=by
      rw [guardRun]
      exact fun normal=>Mpt.Fail.call_not_normal source _ live.code [.const 1#64] (Prod.ext normal rfl)
    rw [lookup_tail_shape.1,sequence_stopped source missingGuard materializeCall stops,guardRun]
    exact Nat.le_trans (Mpt.Fail.call_price source.code live.code [.const 1#64] source rfl) (by omega)
  · rw [present] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=(none,source) := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.presentValue,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [lookup_tail_shape.1,evaluateHOLFiniteState_seq_line780,guardRun]
    exact witness_materialize_call_price data source pointer length heap root database tableBefore dbCell rootCell recordCell
      small lower before heapCell heapArena heapBound aligned live

/-- Complete current root decoder at an actual built node database.
The empty-root comparison, real lookup and all materializer/cache outcomes
are included; neither root readability nor query success is assumed. -/
theorem witness_root_price (data : CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root heap : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤1757412483485 := by
  rcases witness_root_lookup_trace data source (evaluateHOLFiniteState source body).2 root database live.code dbCell rootCell _ rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨current,answer,inner,result,frame,forward,prefixPrice,currentDb,currentRoot,recordCell,continued,endpoint,physical⟩:=entered
    have globals:=congrArg PanSemStateFiniteExact.globals frame
    change current.globals=source.globals at globals
    have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have suffix:=witness_after_lookup_price data current root heap answer (database.of_frame frame) result tableBefore currentDb currentRoot recordCell
      currentHeap heapArena heapBound aligned (live.of_frame frame)
    rw [continued] at suffix
    change current.clock-inner.clock≤1757412483215 at suffix
    change (evaluateHOLFiniteState source body).2.clock=inner.clock at endpoint
    rw [endpoint]
    omega

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_materialize_call_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_after_lookup_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_root_price
