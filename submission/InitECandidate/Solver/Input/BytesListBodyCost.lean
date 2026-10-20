import InitECandidate.Solver.Input.BytesListPackedCost

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete unchanged byte-list hash on main's actual extra-data inputs:
<=32bytes, literal limit1, genuine packing/Merkle/release/length mix and all
non-timeout failures, charged by the real returned chunk count. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+148 := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have price := after_mark_cost entry final p cursor out stp accel chunk zeros n short nextWorkspace
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "limit_chunks" (by decide)).trans limitLocal)
    ((other "out" (by decide)).trans output) heap inputArena arena aligned outArena result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have clock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape.1,body_shape.2.1,body_shape.2.2.1,body_shape.2.2.2.1,body_shape.2.2.2.2]
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "pack_bytes") _ _ _ _ _ (PackBytes.original_code code installed) (PackBytes.globals key code installed different)
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "merkleize") merkleArguments Merkle.formals Merkle.body .one (Merkle.original_code code installed) (Merkle.globals key code installed different))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) (Merkle.release_globals key code different))
      (GlobalEffects.sequence key code _ _
        (GlobalEffects.call_body key code (some none) (ofString "mix_in_length") mixArguments MixLength.formals MixLength.body .one
          (MixLength.original_code code installed) (MixLength.globals key code installed)) (GlobalEffects.returned key code _)))

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.body_cost
#print axioms InitECandidate.Solver.Input.BytesList.globals
