import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix
import InitECandidate.Solver.Mpt.WitnessCoreBodyCost
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

theorem Invariant.loop_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (invariant : Invariant databaseData frontier db limit source cfg)
    (normal : evaluateHOLFiniteState source (.while WitnessCore.condition loopBody)=(none,post)) : StablePrefix source post frontier := by
  let property:=fun current=>(∃ actual,Invariant databaseData frontier db limit current actual) ∧ StablePrefix source current frontier
  have step (current : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : current.code=source.code)
      (valid : property current) (word : BitVec 64)
      (guard : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) WitnessCore.condition=some (.val (.word word)))
      (nonzero : word≠0) (funded : current.clock≠0) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,target)) : property target := by
    obtain ⟨⟨actual,ready⟩,oldMemory⟩:=valid
    have read:=ready.condition databaseData frontier db limit current actual
    have same : goWord actual.running=word:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans guard)))
    have running : actual.running=true:=by
      cases observed : actual.running with
      | false=>apply False.elim; apply nonzero; rw [←same,observed]; rfl
      | true=>rfl
    have ticked:=ready.dec_clock databaseData frontier db limit current actual
    obtain ⟨next,nextInvariant,rank⟩:=ticked.body_normal databaseData frontier db limit (decClockHOLFinite current) target actual running run
    have memory:=ticked.body_prefix databaseData frontier db limit (decClockHOLFinite current) target actual running run
    exact ⟨⟨next,nextInvariant⟩,fun query upper=>(memory query upper).trans (oldMemory query upper)⟩
  exact (Input.loop_invariant source.code (ofString "db") WitnessCore.condition loopBody loop_body_prefix property step source post rfl
    ⟨⟨cfg,invariant⟩,fun _ _=>rfl⟩ normal).2

/-- The complete original238 normal return preserves every older live
persistent word below its fixed entry heap. No future execution is assumed. -/
theorem body_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : StablePrefix source post heap.toNat := by
  have invariant:=initial_invariant databaseData source db pointer length heap cursor limit database tableBefore databaseEq dbCell heapCell heapArena heapBound aligned heapLower live arena before small lower installed
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source post pointer length pointerCell lengthCell (some (.returned returned)) normal
  have safe : Input.LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨finished,loopRun,footerRun⟩:=Input.sequence_returned (ready source pointer length) inner (.while condition loopBody) footer returned
    (safe.summary_full (ready source pointer length)).2.1 continued
  have memory:=invariant.loop_prefix databaseData heap.toNat db limit (ready source pointer length) finished _ loopRun
  obtain ⟨read,innerEq⟩:=Input.return_normal finished inner (localVar "result") returned footerRun
  have restoration:=ProgramPrefix.restoration_frame setup inner
  have pure : Input.LocalEffects.erase post=Input.LocalEffects.erase finished:=by
    rw [postEq]
    have erased:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) restoration
    change Input.LocalEffects.erase (restoreStack inner)=Input.LocalEffects.erase inner at erased
    exact erased.trans (by rw [innerEq]; rfl)
  intro query upper
  exact (congrFun (Input.LocalEffects.memory_of_erase finished post pure) query).trans (memory query upper)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.loop_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_prefix
