import InitECandidate.Solver.Mpt.WitnessCoreBodyCost
import InitECandidate.Solver.Mpt.WitnessCoreRichLoopNormal
import InitECandidate.Solver.Mpt.WitnessCoreBodyNormal
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- The genuine core return retains its final physical loop state as
ownership evidence. The actual footer clears locals and the seven scopes
restore their saved bindings; ordinary storage and runtime fields agree. -/
def RichCompleted (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop:=
  ∃ heap cursor child finished,
    returned=.val (.word child) ∧ RichInvariant input frontier db limit finished ⟨heap,cursor,[],.returning,false⟩ ∧
    finished.locals.lookup (ofString "result")=some (.val (.word child)) ∧
    Input.LocalEffects.erase post=Input.LocalEffects.erase finished ∧ ResultOwned post (max frontier (resultLower [])) heap.toNat child

theorem rich_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : RichCompleted input heap.toNat db limit post returned := by
  have savedBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualCell,heapArena,aligned,nodeBefore,codeBefore⟩:=savedBoundary
  have heapEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have invariant:=initial_invariant input source db pointer length heap cursor limit boundary dbCell heapCell heapArena aligned heapLower arena below before small lower installed
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source post pointer length pointerCell lengthCell (some (.returned returned)) normal
  have safe : Input.LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨finished,loopRun,footerRun⟩:=Input.sequence_returned (ready source pointer length) inner (.while condition loopBody) footer returned
    (safe.summary_full (ready source pointer length)).2.1 continued
  have rich:=RichInvariant.initial input heap.toNat db heap cursor limit (ready source pointer length) invariant
  obtain ⟨nextHeap,nextCursor,child,finalInvariant,resultCell,owned⟩:=rich.loop_normal input heap.toNat db limit (ready source pointer length) finished _ heapLower loopRun
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
  exact ⟨nextHeap,nextCursor,child,finished,returnedEq,finalInvariant,resultCell,pure,
    owned.of_fields finished post child (max heap.toNat (resultLower [])) nextHeap.toNat memory⟩

theorem RichCompleted.to_completed (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : RichCompleted input frontier db limit post returned) : Completed input frontier db limit post returned := by
  obtain ⟨heap,cursor,child,finished,returnedEq,rich,result,pure,owned⟩:=completed
  exact ⟨heap,cursor,child,finished,returnedEq,rich.base,pure,owned⟩

/-- The real footer/scopes retain the completed graph and its exact
returned node even though the returned callee locals have been cleared. -/
theorem RichCompleted.registry (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : RichCompleted input frontier db limit post returned) :
    ∃ heap child,returned=.val (.word child) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      ∃ registry : NodeRegistry post frontier heap db,registry.graph.valid child := by
  obtain ⟨heap,cursor,child,finished,returnedEq,rich,result,pure,owned⟩:=completed
  obtain ⟨active⟩:=rich.registry
  have memory:=Input.LocalEffects.memory_of_erase finished post pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change post.memaddrs=finished.memaddrs at domain
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change post.globals=finished.globals at globals
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=active.nodes.graph.after_agreement finished post 1024 frontier heap.toNat (WitnessValue db)
    active.nodes.values active.nodes.regions active.nodes.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨heap,child,returnedEq,by rw [globals]; exact rich.base.heapCell,⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid child
  rw [validEq]
  exact active.returned rfl child result

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.rich_body_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichCompleted.registry
