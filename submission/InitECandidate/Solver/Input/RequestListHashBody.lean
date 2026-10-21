import InitECandidate.Solver.Input.RequestListHashAllocation
import InitECandidate.Solver.Input.HeapMarkTrace

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem price_merge (price n : Nat) : (price+2)*n+115*n+24208=(price+117)*n+24208 := by
  simp only [Nat.add_mul]
  omega

def price (kind : Kind) (n : Nat) := (kind.record.price+117)*n+24210

theorem after_mark_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag))))
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312)) (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(kind.record.price+117)*n+24209 ∧
      (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark))) := by
  obtain ⟨paid,allocatedFinal,allocatedRun,allocatedEndpoint⟩ := allocation_trace source post roots n bounded workspace.sha.installed count heap arena result run notTimeout
  obtain ⟨final,remaining,endpoint⟩ := after_roots_trace (allocated source roots n) allocatedFinal result allocatedRun
  obtain ⟨round,rootsArena,cursorArena,cursorAligned⟩ := allocation_geometry roots n bounded arena aligned
  let entry := bind (allocated source roots n) "i" 0#64
  have allocatedWorkspace := allocated_workspace source roots stp accel chunk zeros n workspace
  have nextWorkspace := SszHash.Workspace.of_fields (allocated source roots n) entry stp accel chunk zeros allocatedWorkspace rfl rfl (by intro key different; rfl)
  have other (name : String) (a : ofString "i"≠ofString name) (b : ofString "roots"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other (allocated source roots n) "i" name 0#64 a).trans (allocated_other source roots n name b)
  have rootCell : entry.locals.lookup (ofString "roots")=some (.val (.word roots)) :=
    (bind_lookup_other (allocated source roots n) "i" "roots" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  have ready : RoundState entry kind p roots out (cursor roots n) stp accel chunk zeros n 0 :=
    ⟨nextWorkspace,(other "kind" (by decide) (by decide)).trans category,(other "p" (by decide) (by decide)).trans pointer,
      (other "n" (by decide) (by decide)).trans count,(other "sz" (by decide) (by decide)).trans size,rootCell,(other "out" (by decide) (by decide)).trans output,
      bind_lookup_same _ _ _,allocated_heap source roots n round⟩
  have geometry : Geometry kind p roots (cursor roots n) n := ⟨inputArena,rootsArena,aligned,AllocatedBytes.Arena.weaken _ (1280+64*n) 1280 cursorArena (by omega),cursorAligned⟩
  have listArena := AllocatedBytes.Arena.weaken _ (1280+64*n) (832+64*n) cursorArena (by omega)
  have summary := loop_suffix_summary entry final kind p roots out (cursor roots n) mark stp accel chunk zeros n 0 bounded (by omega) ready geometry
    ((other "mark" (by decide) (by decide)).trans saved) listArena outArena result remaining notTimeout
  have cost := summary.1
  rw [Nat.sub_zero,price_merge] at cost
  have monotone := evaluateHOLFiniteState_clock_le entry loopAndSuffix
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [allocatedEndpoint,endpoint]; rfl
  refine ⟨by rw [endpointClock]; omega,?_⟩
  intro value returned
  rw [allocatedEndpoint,endpoint]
  exact summary.2 value returned

/-- Whole unchanged request-list hash at its actual original kind and
record count: real roots allocation, selected fixed-record loop, progressive
list/length mix and final release. Normal returns restore entry heap. -/
theorem body_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag))))
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312)) (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price kind n ∧ (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots))) := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" roots
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name roots different
  have summary := after_mark_summary entry final kind p roots out roots stp accel chunk zeros n bounded nextWorkspace
    ((other "kind" (by decide)).trans category) ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count)
    ((other "sz" (by decide)).trans size) ((other "out" (by decide)).trans output) (bind_lookup_same _ _ _)
    heap inputArena arena aligned outArena result remaining notTimeout
  have cost := summary.1
  have monotone := evaluateHOLFiniteState_clock_le entry afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  refine ⟨?_,?_⟩
  · rw [endpointClock]; unfold price; omega
  · intro value returned; rw [endpoint]; exact summary.2 value returned

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterMark afterRoots loopAndSuffix
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different)
  exact GlobalEffects.declared key code _ _ _ _ (GlobalEffects.sequence key code _ _ (loop_globals key code installed different) (after_loop_globals key code installed different))

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.after_mark_summary
#print axioms InitECandidate.Solver.Input.RequestListHash.body_summary
#print axioms InitECandidate.Solver.Input.RequestListHash.globals
