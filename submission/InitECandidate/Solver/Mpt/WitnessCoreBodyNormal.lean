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
def Completed (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop:=
  ∃ heap cursor child finished,
    returned=.val (.word child) ∧ Invariant input frontier db limit finished ⟨heap,cursor,[],.returning,false⟩ ∧
    Input.LocalEffects.erase post=Input.LocalEffects.erase finished ∧ ResultOwned post (max frontier (resultLower [])) heap.toNat child

theorem body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : Completed input heap.toNat db limit post returned := by
  have savedBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualCell,heapArena,aligned,nodeBefore,codeBefore⟩:=savedBoundary
  have heapEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have invariant:=initial_invariant input source db pointer length heap cursor limit boundary dbCell heapCell heapArena aligned heapLower arena below before small lower installed
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source post pointer length pointerCell lengthCell (some (.returned returned)) normal
  have safe : Input.LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨finished,loopRun,footerRun⟩:=Input.sequence_returned (ready source pointer length) inner (.while condition loopBody) footer returned
    (safe.summary_full (ready source pointer length)).2.1 continued
  obtain ⟨nextHeap,nextCursor,child,finalInvariant,resultCell,owned⟩:=invariant.loop_normal input heap.toNat db limit (ready source pointer length) finished _ loopRun
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
theorem Completed.resume (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : Completed input frontier db limit post returned)
    (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase post)
    (dbCell : target.locals.lookup (ofString "db")=some (.val (.word db))) :
    ∃ heap child,returned=.val (.word child) ∧ RootBoundary input target ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ ResultOwned target (max frontier (resultLower [])) heap.toNat child := by
  obtain ⟨heap,cursor,child,finished,returnedEq,invariant,postPure,owned⟩:=completed
  have wholePure:=pure.trans postPure
  have memory:=Input.LocalEffects.memory_of_erase finished target wholePure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs wholePure
  change target.memaddrs=finished.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be wholePure
  change target.be=finished.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals wholePure
  change target.globals=finished.globals at globals
  have frozen:=invariant.frozen.frame input finished target frontier domain endian (dbCell.trans invariant.dbCell.symm) (by intros; exact congrFun memory _)
  have heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact invariant.heapCell
  have boundary:=frozen.boundary input target frontier heap heapCell invariant.heapArena invariant.aligned invariant.frontierBefore
  exact ⟨heap,child,returnedEq,boundary,heapCell,
    owned.of_fields post target child (max frontier (resultLower [])) heap.toNat (Input.LocalEffects.memory_of_erase post target pure)⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Completed.resume
