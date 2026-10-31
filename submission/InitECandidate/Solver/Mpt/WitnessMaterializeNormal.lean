import InitECandidate.Solver.Mpt.WitnessMptWrapperNormal
import InitECandidate.Solver.Arenas.ScratchCallNormal

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
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
  Input.NoReturn.sequence release (.raise (ofString "RlpErr") (localVar "e"))
    (Input.NoReturn.ignored_call (ofString "scratch_release") [localVar "mark"])
    (Input.NoReturn.raise _ _)

/-- Whole unchanged original240 normal return: derive the actual marked
scratch cursor and caught original239 return, execute the real release,
then retain physical database/heap/fresh-node ownership through every
footer and mark/e/nd scope restoration. -/
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
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    Output databaseData heap.toNat db post returned ∧ post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) ∧ WitnessCore.Stack.StablePrefix source post heap.toNat := by
  by_cases zero : source.clock=0
  · rw [wrapper_shape,evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
    simp only [evalListHOLFinite,evalListHOLExact] at normal
    generalize lookedUp : lookupCodeHOLFinite source.code.lookup (ofString "scratch_mark") []=entry at normal
    cases entry with
    | none=>simp at normal
    | some data=>obtain ⟨functionBody,callee,shape⟩:=data; simp [zero] at normal
  · have markRun:=Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) arena.cursorGlobal (by omega)
    change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at markRun
    rw [wrapper_shape,markRun] at normal
    let marked:=QueryBranch.bind {source with clock:=source.clock-1} "mark" cursor
    let markedPost:=(evaluateHOLFiniteState marked afterMark).2
    have firstEq:=congrArg Prod.fst normal
    change (evaluateHOLFiniteState marked afterMark).1=some (.returned returned) at firstEq
    have markedRun : evaluateHOLFiniteState marked afterMark=(some (.returned returned),markedPost):=Prod.ext firstEq rfl
    have markEnd : post=restore source "mark" markedPost:=(congrArg Prod.snd normal).symm
    obtain ⟨errorPost,errorRun,errorEnd⟩:=Input.ScalarScope.declare_trace marked markedPost "e" (.const 0#64) 0#64 afterError (some (.returned returned)) rfl markedRun
    let errorSource:=QueryBranch.bind marked "e" 0#64
    obtain ⟨readyPost,readyRun,readyEnd⟩:=Input.ScalarScope.declare_trace errorSource errorPost "nd" (.const 0#64) 0#64 afterResult (some (.returned returned)) rfl errorRun
    let ready:=QueryBranch.bind errorSource "nd" 0#64
    have keep (name : String) (notMark : ofString "mark"≠ofString name) (notE : ofString "e"≠ofString name) (notNode : ofString "nd"≠ofString name) :
        ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
      (bind_lookup_other errorSource "nd" name 0#64 notNode).trans ((bind_lookup_other marked "e" name 0#64 notE).trans
        (bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor notMark))
    have readyDb:=(keep "db" (by decide) (by decide) (by decide)).trans dbCell
    have readyPointer:=(keep "p" (by decide) (by decide) (by decide)).trans pointerCell
    have readyLength:=(keep "n" (by decide) (by decide) (by decide)).trans lengthCell
    have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word cursor)):=
      (bind_lookup_other errorSource "nd" "mark" 0#64 (by decide)).trans ((bind_lookup_other marked "e" "mark" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
    have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) childArguments=some (WitnessMaterializeMpt.values db pointer length cursor):=by
      simp [childArguments,WitnessMaterializeMpt.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,readyDb,readyPointer,readyLength,readyMark]
    obtain ⟨callee,called,entryDb,entryPointer,entryLength,entryMark⟩:=WitnessMaterializeMpt.environment ready.code.lookup db pointer length cursor (WitnessMaterializeMpt.original_code source.code installed)
    have never : Input.NoReturn.Never caught:=Input.NoReturn.caught_destination (some (.local,ofString "nd")) (ofString "_decode_witness_node_mpt") childArguments (ofString "RlpErr") (ofString "e") handler handler_no_return
    obtain ⟨afterCall,callRun,footerRun⟩:=Input.sequence_returned ready readyPost caught footer returned (fun value=>never ready value) readyRun
    obtain ⟨funded,built,childReturn,childRun,checked,assigned⟩:=Input.CallNormal.assigned_caught_stops ready afterCall (ofString "nd") (ofString "_decode_witness_node_mpt") childArguments _
      WitnessMaterializeMpt.body callee .one (ofString "RlpErr") (ofString "e") handler args called (fun current _=>handler_stops current) callRun
    let entry:=callEntryStateHOLFinite ready callee
    have entryDatabase:=database.of_frame (show Input.LocalEffects.erase entry=Input.LocalEffects.erase source from rfl)
    have entryArena:=arena.of_fields source entry cursor limit rfl rfl
    obtain ⟨output,priorMemory⟩:=WitnessMaterializeMpt.body_normal databaseData entry built db pointer length heap cursor limit entryDatabase tableBefore databaseEq entryDb entryPointer entryLength heapCell heapArena heapBound aligned heapLower (live.of_frame rfl) entryArena before small lower installed childReturn childRun
    have pureCall : Input.LocalEffects.erase afterCall=Input.LocalEffects.erase built:=by rw [assigned]; rfl
    have afterOutput:=output.of_erase databaseData heap.toNat db built afterCall childReturn pureCall
    have savedOutput:=afterOutput
    obtain ⟨nextHeap,child,returnedEq,heapCellPost,heapArena,heapBound,aligned,grows,scratch,tableAfter,databaseAfter,owned⟩:=savedOutput
    obtain ⟨oldCursor,cursorCell⟩:=scratch
    have afterMark : afterCall.locals.lookup (ofString "mark")=some (.val (.word cursor)):=by
      rw [assigned]
      simp only [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nd"≠ofString "mark" from by decide,if_false]
      exact readyMark
    have releaseArgs : evalListHOLFinite afterCall (h:=fun query=>Classical.propDecidable (afterCall.memaddrs query)) [localVar "mark"]=some [.val (.word cursor)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,afterMark]
    have codeEq:=(Input.evaluation_fields ready afterCall caught none callRun).2.2.2
    have afterInstalled : Input.OriginalCode.Installed afterCall.code:=by rw [codeEq]; exact installed
    obtain ⟨released,releaseRun,returnedRun⟩:=Input.sequence_returned afterCall readyPost release (.return (localVar "nd")) returned
      (fun value=>Input.NoReturn.ignored_call (ofString "scratch_release") [localVar "mark"] afterCall value) footerRun
    obtain ⟨releaseFunded,releaseEq⟩:=Arenas.Scratch.release_call_normal afterCall released cursor oldCursor [localVar "mark"] releaseArgs cursorCell afterInstalled releaseRun
    have releasedOutput : Output databaseData heap.toNat db released childReturn:=by rw [releaseEq]; exact afterOutput.release databaseData heap.toNat db cursor afterCall childReturn
    have nodeCell : released.locals.lookup (ofString "nd")=some childReturn:=by
      rw [releaseEq,assigned]
      simp [setVarHOLFinite,Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]
    obtain ⟨read,footerEq⟩:=Input.return_normal released readyPost (localVar "nd") returned returnedRun
    have actualRead : eval released (localVar "nd")=some childReturn:=by simp [eval,localVar,evalHOLExact,toExact,nodeCell]
    have returnedEq : returned=childReturn:=Option.some.inj (read.symm.trans actualRead)
    have pure : Input.LocalEffects.erase post=Input.LocalEffects.erase released:=by rw [markEnd,errorEnd,readyEnd,footerEq]; rfl
    have cursorPost : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)):=by
      have globals:=congrArg PanSemStateFiniteExact.globals pure
      change post.globals=released.globals at globals
      rw [globals,releaseEq]
      simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]
    refine ⟨by rw [returnedEq]; exact releasedOutput.of_erase databaseData heap.toNat db released post childReturn pure,cursorPost,?_⟩
    intro query earlier
    rw [Input.LocalEffects.memory_of_erase released post pure,releaseEq]
    exact (congrFun (Input.LocalEffects.memory_of_erase built afterCall pureCall) query).trans (priorMemory query earlier)

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.handler_stops
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.handler_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.body_normal
