import InitECandidate.Solver.Input.CurrentVerify.WitnessRootLookup
import InitECandidate.Solver.Mpt.CurrentWitnessMaterializeCost
import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost
import InitECandidate.Solver.Mpt.FailGuard

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch Mpt.WitnessDecodeRoot

theorem witness_materialize_call_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap root : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some (CurrentTable.NodeLookup.presentValue pointer length))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source materializeCall).2.clock≤200274 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) materializeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
    simp [materializeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,recordCell,CurrentTable.NodeLookup.presentValue]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup
    (ofString "_decode_witness_node") (ofString "db") (ofString "p") (ofString "n") Mpt.WitnessMaterialize.body .one
    db pointer length (by decide) (by decide) (by decide) (Mpt.WitnessMaterialize.original_code source.code arena.code)
  rw [lookup_tail_shape.2]
  exact ClockCost.scoped_reached_current source "nd" .one (ofString "_decode_witness_node") materializeArguments _
    Mpt.WitnessMaterialize.body afterMaterialize callee .one 200229 44 args called
    (Mpt.WitnessMaterialize.current_body_price (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal
      small before heapCell heapArena heapBound aligned (arena.of_frame rfl)) (by
      intro target value normal checked
      let ready:=CallNormal.continuationEntry source target "nd" value
      have currentRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
        (CallNormal.continuation_lookup_other source target "nd" "root_hash" value (by decide)).trans rootCell
      have codeEq:=(evaluation_fields (callEntryStateHOLFinite source callee) target Mpt.WitnessMaterialize.body _ normal).2.2.2
      have installed : OriginalCode.Installed ready.code:=by change OriginalCode.Installed target.code; rw [codeEq]; exact arena.code
      exact suffix_cost ready root installed currentRoot)

/-- A missing lookup actually fails at its real guard. A present result
supplies the bounded original input slice used by the actual decoder call. -/
theorem witness_after_lookup_price (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputPointer db root heap : BitVec 64) (start length boundary : Nat) (answer : ValueHOL 64)
    (result : LookupResult input inputPointer start length boundary 1024 answer)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some answer)
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source afterLookup).2.clock≤200274 := by
  rcases result with absent|⟨index,inside,present,allocated,lower,extent,small⟩
  · rw [absent] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=evaluateHOLFiniteState source missingCall := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have stops : (evaluateHOLFiniteState source missingGuard).1≠none:=by
      rw [guardRun]
      exact fun normal=>Mpt.Fail.call_not_normal source _ arena.code [.const 1#64] (Prod.ext normal rfl)
    rw [lookup_tail_shape.1,sequence_stopped source missingGuard materializeCall stops,guardRun]
    exact Nat.le_trans (Mpt.Fail.call_price source.code arena.code [.const 1#64] source rfl) (by omega)
  · rw [present] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=(none,source) := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.presentValue,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [lookup_tail_shape.1,evaluateHOLFiniteState_seq_line780,guardRun]
    exact witness_materialize_call_price source db _ _ heap root dbCell rootCell recordCell small (by omega) heapCell heapArena heapBound aligned arena

/-- Whole unchanged current239 at the actual matching witness/table image.
The lookup derives any successful decode's input; all absent, malformed,
allocator, handler and timeout outcomes are included. -/
theorem witness_root_price {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap root heap : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤200544 := by
  rcases witness_root_lookup_trace witness arena.code tableImage dbCell rootCell _ rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨current,answer,inner,result,frame,forward,prefixPrice,currentDb,currentRoot,recordCell,continued,endpoint,physical⟩:=entered
    have globals:=congrArg PanSemStateFiniteExact.globals frame
    change current.globals=source.globals at globals
    have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have suffix:=witness_after_lookup_price input current pointer table root heap start length boundary answer result currentDb currentRoot recordCell
      before currentHeap heapArena heapBound aligned (arena.of_frame frame)
    rw [continued] at suffix
    change current.clock-inner.clock≤200274 at suffix
    change (evaluateHOLFiniteState source body).2.clock=inner.clock at endpoint
    rw [endpoint]
    omega

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_after_lookup_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_root_price
