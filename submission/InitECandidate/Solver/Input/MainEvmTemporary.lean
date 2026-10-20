import InitECandidate.Solver.Input.MainEvmProgram
import InitECandidate.Solver.Input.InitializerFields
import InitECandidate.Solver.WitnessRadix.AllocationCall

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  QueryBranch.bind {source with clock := source.clock - 1} "mark" (BitVec.ofNat 64 cursor)
def stringAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  QueryBranch.bind (PersistentAlloc.post {marked source cursor with clock := (marked source cursor).clock - 1} (BitVec.ofNat 64 cursor) 40#64) "s" (BitVec.ofNat 64 cursor)
def stringWritten (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerBytes.written (stringAllocated source cursor) (BitVec.ofNat 64 cursor) 0 literal
def stringReleased (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  HeapScope.releasePost {stringWritten source cursor with clock := (stringWritten source cursor).clock - 1} (BitVec.ofNat 64 cursor)
def topicReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  {InitializerAllocations.template (stringReleased source cursor) cursor [topicAction] with clock := source.clock - 4}

theorem temporary_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (topicReady source cursor) = InitializerAllocations.context source := by
  unfold topicReady
  rw [InitializerAllocations.context_clock,InitializerAllocations.template_context]
  rfl

theorem temporary_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (topicReady source cursor).globals := by
  apply InitializerAllocations.template_scalars
  exact (scalars.update (ofString "heap_ptr") (PersistentAlloc.rounded (BitVec.ofNat 64 cursor) 40#64)).update (ofString "heap_ptr") (BitVec.ofNat 64 cursor)

/-- Execute the original lexical mark/string allocation, all thirty-three
stores, release, and topic allocation. The released bytes remain readable;
the topic deliberately reuses their address. -/
theorem temporary_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 40 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (let output := evaluateHOLFiniteState (topicReady source cursor) afterTopicAllocation
       (output.1,restore source "mark" (restore (marked source cursor) "s" output.2))) := by
  classical
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have marking := HeapScope.mark_call_execute source (BitVec.ofNat 64 cursor) "mark" afterMark heap
    (HeapScope.mark_original_code source.code installed) (by omega)
  have allocating := PersistentAlloc.call_execute (marked source cursor) "s" [.const 40#64] stringStores (BitVec.ofNat 64 cursor) 40#64 rfl
    (PersistentAlloc.original_code _ installed) heap (by rw [number]; exact room) (by change 1 ≤ source.clock - 1; omega)
  have sBinding : lookupKvarHOLFinite .local (ofString "s") (stringAllocated source cursor) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp [lookupKvarHOLFinite,stringAllocated,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have bytesRun := InitializerBytes.execute (stringAllocated source cursor) .local "s" (BitVec.ofNat 64 cursor) 0 40 literal afterString
    sBinding domain ⟨by rw [number]; exact lower,by rw [number]; exact room⟩ (by rw [literal_length]; omega)
  have markBinding : (stringWritten source cursor).locals.lookup (ofString "mark") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp [stringWritten,InitializerBytes.written,stringAllocated,QueryBranch.bind,setVarHOLFinite,marked,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have releaseArgs : evalListHOLFinite (stringWritten source cursor) (h := fun address => Classical.propDecidable ((stringWritten source cursor).memaddrs address))
      [.var .local (ofString "mark")] = some [.val (.word (BitVec.ofNat 64 cursor))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,markBinding]
  have oldHeap : (stringWritten source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded (BitVec.ofNat 64 cursor) 40#64))) := by
    simp [stringWritten,InitializerBytes.written,stringAllocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have releasing := HeapScope.release_call_execute (stringWritten source cursor) (BitVec.ofNat 64 cursor) _ _ releaseArgs oldHeap
    (HeapScope.release_original_code _ installed) (by change 1 ≤ source.clock - 1 - 1; omega)
  have releasedHeap : (stringReleased source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp [stringReleased,HeapScope.releasePost,HolFiniteMapExact.update,FUPDATE]
  have releasedScalars : OriginalScalarGlobals.Scalars (stringReleased source cursor).globals :=
    (scalars.update (ofString "heap_ptr") (PersistentAlloc.rounded (BitVec.ofNat 64 cursor) 40#64)).update (ofString "heap_ptr") (BitVec.ofNat 64 cursor)
  have topicAllocation := InitializerAllocations.execute_prefix (stringReleased source cursor) cursor [topicAction] afterTopicAllocation installed releasedScalars releasedHeap
    (by intro action member; have same := List.mem_singleton.mp member; subst action; exact actions_valid.1)
    (by change cursor + (32 + 0) ≤ 33806089496; omega) aligned (by change 1 ≤ source.clock - 1 - 1 - 1; omega)
  have topicClock : (stringReleased source cursor).clock - [topicAction].length = source.clock - 4 := by
    change source.clock - 1 - 1 - 1 - 1 = _; omega
  simp only [topicClock] at topicAllocation
  rw [body_shape,marking]
  change (let output := evaluateHOLFiniteState (marked source cursor) afterMark; (output.1,restore source "mark" output.2)) = _
  simp only [afterMark,allocating]
  change (let output := evaluateHOLFiniteState (stringAllocated source cursor) stringStores; (output.1,restore source "mark" (restore (marked source cursor) "s" output.2))) = _
  rw [stringStores,bytesRun]
  have releaseStep : evaluateHOLFiniteState (stringWritten source cursor) afterString = evaluateHOLFiniteState (stringReleased source cursor) afterRelease :=
    StateSteps.next_sequence _ _ releaseCall afterRelease releasing (by change source.clock - 1 - 1 - 1 ≤ source.clock - 1 - 1; omega)
  change (let output := evaluateHOLFiniteState (stringWritten source cursor) afterString; (output.1,restore source "mark" (restore (marked source cursor) "s" output.2))) = _
  rw [releaseStep]
  simp only [afterRelease,topicAllocation,topicReady]

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.temporary_context
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.temporary_scalars
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.temporary_execute
