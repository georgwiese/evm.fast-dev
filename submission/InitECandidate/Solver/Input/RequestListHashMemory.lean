import InitECandidate.Solver.Input.RequestListHashLoopMemory
import InitECandidate.Solver.Input.RequestListHashCall
import InitECandidate.Solver.Input.PListChunksMemory

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual request-list root hashing and release preserve decoded memory. -/
theorem after_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (arena : AllocatedBytes.Arena cursor (832+64*n))
    (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args := list_arguments source roots out n actual.root actual.count actual.output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold afterLoop at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ FixedHash.releaseSuffix value (safe.summary_full source).2.1 run
  have front := PListChunks.call_memory source middle roots cursor out (BitVec.ofNat 64 n) stp accel chunk zeros query n bounded protection actual.heap rootsArena arena aligned outArena below outAway listArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have tail := HeapScope.release_return_memory middle post [localVar "mark"] query (fields.2.2.2.symm ▸ actual.workspace.sha.installed) value remaining
  exact tail.trans front

/-- Actual normal record-loop exit derives the current root/count/workspace
used by the reached original list hash. -/
theorem loop_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (protection : SszHash.Protected source stp accel chunk zeros query) (geometry : Geometry kind p roots cursor n)
    (arena : AllocatedBytes.Arena cursor (832+64*n)) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post loop afterLoop value ((loop_local (ofString "mark") (by decide)).summary_full source).2.1 run
  have front := loop_memory source middle kind p roots out cursor stp accel chunk zeros query n index bounded inside actual protection geometry below rootsAway normal
  obtain ⟨position,positionBound,current⟩ := loop_normal source middle kind p roots out cursor stp accel chunk zeros n index bounded inside actual geometry normal
  have currentProtection := protection.with_workspace source middle stp accel chunk zeros query current.workspace
  exact (after_loop_memory middle post kind p roots out cursor stp accel chunk zeros query n position bounded current currentProtection geometry.rootsArena arena geometry.aligned outArena below outAway value remaining).trans front

/-- Original roots allocation and counter scope compose with the real loop
and root-hash continuation; decoded words stay below allocated storage. -/
theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag))))
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312))
    (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<roots.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨paid,allocatedFinal,allocatedRun,allocatedEndpoint⟩ := allocation_trace source post roots n bounded protection.workspace.sha.installed count heap arena (some (.returned value)) run (by simp)
  obtain ⟨final,remaining,endpoint⟩ := after_roots_trace (allocated source roots n) allocatedFinal (some (.returned value)) allocatedRun
  obtain ⟨round,rootsArena,cursorArena,cursorAligned⟩ := allocation_geometry roots n bounded arena aligned
  let entry := bind (allocated source roots n) "i" 0#64
  have allocatedWorkspace := allocated_workspace source roots stp accel chunk zeros n protection.workspace
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
  have entryProtection := protection.with_workspace source entry stp accel chunk zeros query nextWorkspace
  have number : (cursor roots n).toNat=roots.toNat+amount n := byteAddress_toNat roots (amount n) (by have h:=arena.upper; unfold amount; omega)
  have frame := loop_suffix_memory entry final kind p roots out (cursor roots n) stp accel chunk zeros query n 0 bounded (by omega) ready entryProtection geometry listArena outArena
    (by rw [number]; unfold amount; omega) (CopyGeneral.Away.after roots query (32*n) aligned (by have h:=arena.upper; omega) below) outAway value remaining
  rw [allocatedEndpoint,endpoint]
  exact frame

/-- Whole unchanged request-list body preserves protected input and decoded
metadata through every actual normal record hash and final root hash. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag))))
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312))
    (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<roots.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" roots
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name roots different
  have frame := after_mark_memory entry final kind p roots out stp accel chunk zeros query n bounded nextProtection
    ((other "kind" (by decide)).trans category) ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count)
    ((other "sz" (by decide)).trans size) ((other "out" (by decide)).trans output) heap inputArena arena aligned outArena below outAway value remaining
  rw [endpoint]
  exact frame

/-- Genuine original five-word caller inherits the whole request-list frame. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312))
    (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<roots.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values kind p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_request_list") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,kindLocal,pLocal,nLocal,sizeLocal,outLocal⟩ := environment source.code.lookup kind p n out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_request_list") arguments (values kind p n out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target kind p roots out stp accel chunk zeros query n bounded
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) kindLocal pLocal nLocal sizeLocal outLocal heap inputArena arena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.after_loop_memory
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_suffix_memory
#print axioms InitECandidate.Solver.Input.RequestListHash.after_mark_memory
#print axioms InitECandidate.Solver.Input.RequestListHash.body_memory

#print axioms InitECandidate.Solver.Input.RequestListHash.call_memory
