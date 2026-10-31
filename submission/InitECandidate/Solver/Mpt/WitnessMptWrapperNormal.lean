import InitECandidate.Solver.Mpt.WitnessMaterializeOutput
import InitECandidate.Solver.Mpt.WitnessCoreBodyPrefix
import InitECandidate.Solver.Mpt.WitnessMptWrapperTrace
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.NoReturnIgnored
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

theorem handler_stops : Input.NoFallthrough handler := by
  apply Input.NoFallthrough.sequence
  intro current
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem handler_no_return : Input.NoReturn.Never handler :=
  Input.NoReturn.sequence WitnessMaterialize.release (.raise (ofString "MptErr") (localVar "e"))
    (Input.NoReturn.ignored_call (ofString "scratch_release") [localVar "mark"])
    (Input.NoReturn.raise _ _)

/-- A genuine normal original239 return must come from the real core
return: its actual release/rethrow handler cannot fall through. The real
assigned result, footer and e/nd restorations retain physical ownership. -/
theorem body_normal (databaseData : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (database : Input.CurrentTable.NodeLookup.Database source databaseData)
    (tableBefore : (Input.CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤heap.toNat) (databaseEq : db=databaseData.table)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) (heapLower : 2701131776≤heap.toNat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2701131776≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : WitnessMaterialize.Output databaseData heap.toNat db post returned ∧ WitnessCore.Stack.StablePrefix source post heap.toNat := by
  rw [wrapper_shape] at normal
  obtain ⟨errorPost,errorRun,errorEnd⟩:=Input.ScalarScope.declare_trace source post "e" (.const 0#64) 0#64 afterError (some (.returned returned)) rfl normal
  let errorSource:=QueryBranch.bind source "e" 0#64
  obtain ⟨readyPost,readyRun,readyEnd⟩:=Input.ScalarScope.declare_trace errorSource errorPost "nd" (.const 0#64) 0#64 afterResult (some (.returned returned)) rfl errorRun
  let ready:=QueryBranch.bind errorSource "nd" 0#64
  have keep (name : String) (notE : ofString "e"≠ofString name) (notNode : ofString "nd"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other errorSource "nd" name 0#64 notNode).trans (bind_lookup_other source "e" name 0#64 notE)
  have readyDb:=(keep "db" (by decide) (by decide)).trans dbCell
  have readyPointer:=(keep "p" (by decide) (by decide)).trans pointerCell
  have readyLength:=(keep "n" (by decide) (by decide)).trans lengthCell
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) childArguments=some (WitnessMaterialize.values db pointer length):=by
    simp [childArguments,WitnessMaterialize.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,readyDb,readyPointer,readyLength]
  obtain ⟨callee,called,entryDb,entryPointer,entryLength⟩:=WitnessCore.environment ready.code.lookup db pointer length (WitnessCore.original_code source.code installed)
  have never : Input.NoReturn.Never caught:=Input.NoReturn.caught_destination (some (.local,ofString "nd")) (ofString "_decode_witness_node_body") childArguments (ofString "MptErr") (ofString "e") handler handler_no_return
  obtain ⟨afterCall,callRun,footerRun⟩:=Input.sequence_returned ready readyPost caught footer returned (fun value=>never ready value) readyRun
  obtain ⟨funded,built,childReturn,childRun,checked,assigned⟩:=Input.CallNormal.assigned_caught_stops ready afterCall (ofString "nd") (ofString "_decode_witness_node_body") childArguments _
    WitnessCore.body callee .one (ofString "MptErr") (ofString "e") handler args called (fun current _=>handler_stops current) callRun
  let entry:=callEntryStateHOLFinite ready callee
  have entryDatabase:=database.of_frame (show Input.LocalEffects.erase entry=Input.LocalEffects.erase source from rfl)
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  have completed:=WitnessCore.Stack.body_normal databaseData entry built db pointer length heap cursor limit entryDatabase tableBefore databaseEq entryDb entryPointer entryLength heapCell heapArena heapBound aligned heapLower (live.of_frame rfl) entryArena before small lower installed childReturn childRun
  have priorMemory:=WitnessCore.Stack.body_prefix databaseData entry built db pointer length heap cursor limit entryDatabase tableBefore databaseEq entryDb entryPointer entryLength heapCell heapArena heapBound aligned heapLower (live.of_frame rfl) entryArena before small lower installed childReturn childRun
  have output:=WitnessMaterialize.Output.of_completed databaseData heap.toNat db limit built childReturn completed
  obtain ⟨read,footerEq⟩:=Input.return_normal afterCall readyPost (localVar "nd") returned footerRun
  have nodeCell : afterCall.locals.lookup (ofString "nd")=some childReturn:=by
    rw [assigned]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have actualRead : eval afterCall (localVar "nd")=some childReturn:=by simp [eval,localVar,evalHOLExact,toExact,nodeCell]
  have returnedEq : returned=childReturn:=Option.some.inj (read.symm.trans actualRead)
  have pure : Input.LocalEffects.erase post=Input.LocalEffects.erase built:=by
    rw [errorEnd,readyEnd,footerEq,assigned]
    rfl
  rw [returnedEq]
  refine ⟨output.of_erase databaseData heap.toNat db built post childReturn pure,?_⟩
  intro query earlier
  exact (congrFun (Input.LocalEffects.memory_of_erase built post pure) query).trans (priorMemory query earlier)

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.handler_stops
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.handler_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.body_normal
