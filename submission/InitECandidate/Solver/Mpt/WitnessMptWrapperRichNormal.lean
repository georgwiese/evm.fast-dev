import InitECandidate.Solver.Mpt.WitnessMptWrapperNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeRichOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- The genuine original239 return retains the completed bounded closed
node registry through its actual caught core call, footer and scopes. -/
theorem rich_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : WitnessMaterialize.RichOutput input heap.toNat db post returned := by
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
  have entryBoundary:=boundary.erase_frame input source entry rfl (entryDb.trans dbCell.symm)
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  have completed:=WitnessCore.Stack.rich_body_normal input entry built db pointer length heap cursor limit entryBoundary entryDb entryPointer entryLength heapCell heapLower entryArena below before small lower installed childReturn childRun
  have output:=WitnessMaterialize.RichOutput.of_completed input heap.toNat db limit built childReturn completed
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
  exact output.of_erase input heap.toNat db built post childReturn pure


end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.rich_body_normal
