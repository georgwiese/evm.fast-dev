import InitECandidate.Solver.Mpt.WitnessCoreBodyCost
import InitECandidate.Solver.Mpt.WitnessCoreLoopNormal
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- The genuine core return retains its final physical loop state as
ownership evidence. The actual footer clears locals and the seven scopes
restore their saved bindings; ordinary storage and runtime fields agree. -/
def Completed (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop:=
  ∃ heap cursor child finished,
    returned=.val (.word child) ∧ Invariant databaseData frontier db limit finished ⟨heap,cursor,[],.returning,false⟩ ∧
    Input.LocalEffects.erase post=Input.LocalEffects.erase finished ∧ ResultOwned post (max frontier (resultLower [])) heap.toNat child

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
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : Completed databaseData heap.toNat db limit post returned := by
  have invariant:=initial_invariant databaseData source db pointer length heap cursor limit database tableBefore databaseEq dbCell heapCell heapArena heapBound aligned heapLower live arena before small lower installed
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source post pointer length pointerCell lengthCell (some (.returned returned)) normal
  have safe : Input.LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨finished,loopRun,footerRun⟩:=Input.sequence_returned (ready source pointer length) inner (.while condition loopBody) footer returned
    (safe.summary_full (ready source pointer length)).2.1 continued
  obtain ⟨nextHeap,nextCursor,child,finalInvariant,resultCell,owned⟩:=invariant.loop_normal databaseData heap.toNat db limit (ready source pointer length) finished _ loopRun
  obtain ⟨read,innerEq⟩:=Input.return_normal finished inner (localVar "result") returned footerRun
  have actualRead : eval finished (localVar "result")=some (.val (.word child)):=by
    simp [eval,localVar,evalHOLExact,toExact,resultCell]
  have returnedEq : returned=.val (.word child):=Option.some.inj (read.symm.trans actualRead)
  have restoration:=ProgramPrefix.restoration_frame setup inner
  have pure : Input.LocalEffects.erase post=Input.LocalEffects.erase finished:=by
    rw [postEq]
    have erased:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) restoration
    change Input.LocalEffects.erase (restoreStack inner)=Input.LocalEffects.erase inner at erased
    exact erased.trans (by rw [innerEq]; rfl)
  have memory:=Input.LocalEffects.memory_of_erase finished post pure
  exact ⟨nextHeap,nextCursor,child,finished,returnedEq,finalInvariant,pure,
    owned.of_fields finished post child (max heap.toNat (resultLower [])) nextHeap.toNat memory⟩

/-- Reinstalling the actual caller locals at a genuine call continuation
recovers the current helper boundary from the completed core's own final
heap/databases. No successful later parse or lookup is a premise. -/
theorem Completed.resume (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (post target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : Completed databaseData frontier db limit post returned)
    (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase post)
    (dbCell : target.locals.lookup (ofString "db")=some (.val (.word db))) :
    ∃ heap child,returned=.val (.word child) ∧ Input.CurrentTable.NodeLookup.Database target databaseData ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧ frontier≤heap.toNat ∧ Rlp.LiveArena target ∧ ResultOwned target (max frontier (resultLower [])) heap.toNat child := by
  obtain ⟨heap,cursor,child,finished,returnedEq,invariant,postPure,owned⟩:=completed
  have wholePure:=pure.trans postPure
  have memory:=Input.LocalEffects.memory_of_erase finished target wholePure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs wholePure
  change target.memaddrs=finished.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be wholePure
  change target.be=finished.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals wholePure
  change target.globals=finished.globals at globals
  have database:=invariant.database.of_frame wholePure
  have live:=invariant.live.of_frame wholePure
  have heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact invariant.heapCell
  exact ⟨heap,child,returnedEq,database,heapCell,invariant.heapArena,invariant.heapBound,invariant.aligned,invariant.frontierBefore,live,
    owned.of_fields post target child (max frontier (resultLower [])) heap.toNat (Input.LocalEffects.memory_of_erase post target pure)⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Completed.resume
