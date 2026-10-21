import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix
import InitECandidate.Solver.Mpt.WitnessCoreBodyCost
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

theorem Invariant.loop_prefix (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (invariant : Invariant input frontier db limit source cfg)
    (normal : evaluateHOLFiniteState source (.while WitnessCore.condition loopBody)=(none,post)) : StablePrefix source post frontier := by
  let property:=fun current=>(∃ actual,Invariant input frontier db limit current actual) ∧ StablePrefix source current frontier
  have step (current : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : current.code=source.code)
      (valid : property current) (word : BitVec 64)
      (guard : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) WitnessCore.condition=some (.val (.word word)))
      (nonzero : word≠0) (funded : current.clock≠0) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,target)) : property target := by
    obtain ⟨⟨actual,ready⟩,oldMemory⟩:=valid
    have read:=ready.condition input frontier db limit current actual
    have same : goWord actual.running=word:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans guard)))
    have running : actual.running=true:=by
      cases observed : actual.running with
      | false=>apply False.elim; apply nonzero; rw [←same,observed]; rfl
      | true=>rfl
    have ticked:=ready.dec_clock input frontier db limit current actual
    obtain ⟨next,nextInvariant,rank⟩:=ticked.body_normal input frontier db limit (decClockHOLFinite current) target actual running run
    have memory:=ticked.body_prefix input frontier db limit (decClockHOLFinite current) target actual running run
    exact ⟨⟨next,nextInvariant⟩,fun query lower upper=>(memory query lower upper).trans (oldMemory query lower upper)⟩
  exact (Input.loop_invariant source.code (ofString "db") WitnessCore.condition loopBody loop_body_prefix property step source post rfl
    ⟨⟨cfg,invariant⟩,fun _ _ _=>rfl⟩ normal).2

/-- The complete original238 normal return preserves every older live
persistent word below its fixed entry heap. No future execution is assumed. -/
theorem body_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : StablePrefix source post heap.toNat := by
  have savedBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualCell,heapArena,aligned,nodeBefore,codeBefore⟩:=savedBoundary
  have heapEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have invariant:=initial_invariant input source db pointer length heap cursor limit boundary dbCell heapCell heapArena aligned heapLower arena below before small lower installed
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source post pointer length pointerCell lengthCell (some (.returned returned)) normal
  have safe : Input.LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨finished,loopRun,footerRun⟩:=Input.sequence_returned (ready source pointer length) inner (.while condition loopBody) footer returned
    (safe.summary_full (ready source pointer length)).2.1 continued
  have memory:=invariant.loop_prefix input heap.toNat db limit (ready source pointer length) finished _ loopRun
  obtain ⟨read,innerEq⟩:=Input.return_normal finished inner (localVar "result") returned footerRun
  have restoration:=ProgramPrefix.restoration_frame setup inner
  have pure : Input.LocalEffects.erase post=Input.LocalEffects.erase finished:=by
    rw [postEq]
    have erased:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) restoration
    change Input.LocalEffects.erase (restoreStack inner)=Input.LocalEffects.erase inner at erased
    exact erased.trans (by rw [innerEq]; rfl)
  intro query lower upper
  exact (congrFun (Input.LocalEffects.memory_of_erase finished post pure) query).trans (memory query lower upper)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.loop_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_prefix
