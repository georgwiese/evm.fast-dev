import InitECandidate.Solver.Input.RequestsHashPipeline
import InitECandidate.Solver.Input.AllocationTrace
import InitECandidate.Solver.Input.HeapMarkTrace

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} ch 160#64) "ch" ch

theorem rounded_roots (ch : BitVec 64) (arena : AllocatedBytes.Arena ch 160) (aligned : ch.toNat%8=0) : PersistentAlloc.rounded ch 160#64=ch+160#64 := by
  have upper:=arena.upper
  have number : (ch+160#64).toNat=ch.toNat+160 := BitVec.toNat_add_of_lt (by change ch.toNat+160<2^64; omega)
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat ch 160#64 (by change ch.toNat+160+7<2^64; omega),number]
  change (ch.toNat+160+7)/8*8=ch.toNat+160
  omega

/-- Actual roots160 allocation derives its own caller funding and feeds the
original five-list pipeline with exact current decoded metadata. -/
theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤pipelinePrice RequestListHash.kinds counts+1 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values 160#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,allocationArguments,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL]
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "ch" allocationArguments afterAllocation ch 160#64 args
    (PersistentAlloc.original_code source.code workspace.sha.installed) heap (by change ch.toNat+160≤33806089496; exact geometry.rootsArena.upper) result run notTimeout
  let entry := allocated source ch
  change evaluateHOLFiniteState entry afterAllocation=(result,final) at remaining
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 160#64)))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have other (name : String) (different : ofString "ch"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "ch" name ch different
  have nextHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (ch+160#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 160#64)))).lookup _=_
    rw [rounded_roots ch geometry.rootsArena geometry.rootsAligned]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have ready : Ready entry rq ch out (ch+160#64) stp accel chunk zeros pointers counts :=
    ⟨nextWorkspace,(other "rq" (by decide)).trans requests,bind_lookup_same _ _ _,(other "out" (by decide )).trans output,⟨image.fields⟩,nextHeap⟩
  have price := pipeline_cost RequestListHash.kinds entry final rq ch out (ch+160#64) stp accel chunk zeros pointers counts capacity ready geometry separation result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry afterAllocation
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have clock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

/-- Whole unchanged original request hash, including actual mark/allocation,
five decoded lists, five-field container and final release. This bounds all
observed non-timeout outcomes using actual per-kind counts. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤1827*counts .deposit+988*counts .wdreq+1364*counts .cons+1652*counts .bdep+813*counts .bexit+145844 := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name ch different
  have price := after_mark_cost entry final rq ch out stp accel chunk zeros pointers counts capacity nextWorkspace
    ((other "rq" (by decide)).trans requests) ((other "out" (by decide )).trans output) ⟨image.fields⟩ heap geometry separation result remaining notTimeout
  rw [pipeline_price] at price
  have monotone := evaluateHOLFiniteState_clock_le entry afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have clock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.rounded_roots
#print axioms InitECandidate.Solver.Input.RequestsHash.after_mark_cost
#print axioms InitECandidate.Solver.Input.RequestsHash.body_cost
