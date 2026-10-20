import InitECandidate.Solver.Input.PBytesPackedCost

namespace InitECandidate.Solver.Input.PBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole unchanged progressive byte-list hash: real mark, actual packed
buffer/count return, progressive hash, length mix and release. Source-clock
work is charged by actual bytes/chunks, with all non-timeout failures kept. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+24282 := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have price := after_mark_cost entry final p cursor out stp accel chunk zeros n small nextWorkspace
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output)
    heap inputArena arena aligned outArena result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have clock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

/-- Every actual byte-list hash outcome retains initialized nonheap globals.
The original allocator/release effects are confined to its real heap cursor. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterMark afterPack afterList
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "pack_bytes") _ _ _ _ _ (PackBytes.original_code code installed) (PackBytes.globals key code installed different)
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "htr_plist_chunks") listArguments PListChunks.formals PListChunks.body .one (PListChunks.original_code code installed) (PListChunks.globals key code installed different))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) (Merkle.release_globals key code different)) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.PBytes

#print axioms InitECandidate.Solver.Input.PBytes.body_cost
#print axioms InitECandidate.Solver.Input.PBytes.globals
