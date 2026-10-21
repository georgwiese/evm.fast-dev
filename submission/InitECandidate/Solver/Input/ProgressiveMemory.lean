import InitECandidate.Solver.Input.ProgressiveSuffixMemory
import InitECandidate.Solver.Input.ProgressiveCallCost

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete original progressive Merkle memory frame. The original
allocation/mark scopes are retained; no data-dependent digest property or
future call success is assumed. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots out zeros stp accel chunk query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (temporaryArena : AllocatedBytes.Arena roots (832+64*n))
    (aligned : roots.toNat%8=0) (outputArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<roots.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  let workspace := protection.workspace.sha
  rw [allocation_shape.1] at run
  obtain ⟨markPaid,markedFinal,markedRun,markEndpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.installed) (some (.returned value)) run (by simp)
  let marked := bind {source with clock:=source.clock-1} "mark" roots
  have markedOther (name : String) (different : ofString "mark"≠ofString name) : marked.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name roots different
  have prefixArena := AllocatedBytes.Arena.weaken roots (832+64*n) 800 temporaryArena (by omega)
  obtain ⟨allocationPaid,allocatedFinal,allocatedRun,allocationEndpoint⟩ := allocation_prefix marked markedFinal roots workspace.installed heap prefixArena aligned (some (.returned value)) markedRun (by simp)
  let entry := initialized marked roots
  have cells := initialized_cells marked roots
  have other (name : String) (a : ofString "roots"≠ofString name) (b : ofString "acc"≠ofString name) (c : ofString "k"≠ofString name)
      (d : ofString "off"≠ofString name) (e : ofString "size"≠ofString name) (f : ofString "mark"≠ofString name) :
      entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (initialized_other marked roots name a b c d e).trans (markedOther name f)
  have entryGlobals (key : MlS) (different : key≠ofString "heap_ptr") : entry.globals.lookup key=source.globals.lookup key :=
    initialized_global_other marked roots key different
  have entryProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl entryGlobals
  have ready : RoundState entry p roots (temporary roots) zeros stp accel n 0 :=
    ⟨(other "p" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pointer,cells.1,
      (other "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans count,
      cells.2.2.2.1,cells.2.2.2.2,cells.2.2.1,initialized_heap marked roots prefixArena aligned,
      (entryGlobals (ofString "zero_hashes") (by decide)).trans protection.workspace.zerosLocal,entryProtection.workspace.sha⟩
  obtain ⟨rootsArena,accArena,bufferArena,accAligned,bufferAligned⟩ := initialized_geometry roots n temporaryArena aligned
  have mapped : Geometry p roots (temporary roots) zeros n := ⟨inputArena,rootsArena,bufferArena,bufferAligned,protection.workspace.zeroArena⟩
  have geometry := allocation_geometry roots prefixArena aligned
  have rootsAway := CopyGeneral.Away.after roots query 768 aligned (by have h:=rootsArena.upper; omega) below
  have accAway := CopyGeneral.Away.after (accPointer roots) query 32 accAligned (by have h:=accArena.upper; omega) (by rw [geometry.1]; omega)
  have currentMemory := dense_memory entry allocatedFinal p roots (temporary roots) zeros stp accel chunk (accPointer roots) out query n 0 bounded (by decide)
    ready entryProtection mapped cells.2.1 ((other "out" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans output)
    accArena outputArena accAligned (by rw [geometry.2.1]; omega) rootsAway accAway outAway value allocatedRun
  rw [markEndpoint,allocationEndpoint]
  exact currentMemory

/-- Actual ignored original progressive caller inherits the complete normal
memory frame at its real ABI and current temporary/output geometry. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots out zeros stp accel chunk query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (temporaryArena : AllocatedBytes.Arena roots (832+64*n))
    (aligned : roots.toNat%8=0) (outputArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<roots.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p (BitVec.ofNat 64 n) out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize_progressive") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p (BitVec.ofNat 64 n) out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "merkleize_progressive") arguments (values p (BitVec.ofNat 64 n) out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p roots out zeros stp accel chunk query n bounded
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) pLocal nLocal outLocal heap inputArena temporaryArena aligned outputArena below outAway value evaluated) run

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.body_memory
#print axioms InitECandidate.Solver.Input.Progressive.call_memory
