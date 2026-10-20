import InitECandidate.Solver.Input.BytesVectorPackedCost
import InitECandidate.Solver.Input.BytesVectorShortCost

namespace InitECandidate.Solver.Input.BytesVector
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def price (n depth : Nat) := if n≤32 then n/8+10 else n/8+115*PackBytes.chunks n+55*depth+89

/-- Whole original byte-vector hash, retaining its actual small-vector
fast path. Longer inputs use their real packing tuple and count-dependent
dense Merkle tree; all actual non-timeout failing prefixes are included. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32) (outAligned : out.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price n depth := by
  by_cases short : n≤32
  · have bound := short_body_cost source p out n short workspace.sha.installed workspace.sha.domain pointer count output inputArena outArena outAligned
    rw [run] at bound
    simpa only [price,if_pos short] using bound
  · rw [long_entry source n small (by omega) count,body_shape.2.1] at run
    obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
      (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
    let entry := bind {source with clock:=source.clock-1} "mark" cursor
    have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
    have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
      bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
    have bound := after_mark_cost entry final p cursor out stp accel chunk zeros n depth small depthSmall depthBound nextWorkspace
      ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output) heap inputArena arena aligned outArena result remaining notTimeout
    have monotone := evaluateHOLFiniteState_clock_le entry afterMark
    rw [remaining] at monotone
    change final.clock≤entry.clock at monotone
    have clock : entry.clock=source.clock-1 := rfl
    have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
    rw [price,if_neg short,endpointClock]
    omega

/-- All nonheap globals survive every original vector-hash outcome, on both
branches and with the real pack/Merkle/heap helper code installed. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape.1,body_shape.2.1,body_shape.2.2.1,body_shape.2.2.2]
  unfold guard shortBody afterMerkle
  apply GlobalEffects.sequence
  · exact GlobalEffects.conditional key code _ _ _
      (GlobalEffects.sequence key code _ _
        (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code code installed) (Zero.globals key code))
        (GlobalEffects.sequence key code _ _
          (GlobalEffects.call_body key code (some none) (ofString "memcpy") copyArguments CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code)) (GlobalEffects.returned key code _)))
      (GlobalEffects.skip key code)
  · apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
    apply GlobalEffects.scoped_body key code _ _ (ofString "pack_bytes") _ _ _ _ _ (PackBytes.original_code code installed) (PackBytes.globals key code installed different)
    exact GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "merkleize") merkleArguments Merkle.formals Merkle.body .one (Merkle.original_code code installed) (Merkle.globals key code installed different))
      (GlobalEffects.sequence key code _ _
        (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one (HeapScope.release_original_code code installed) (Merkle.release_globals key code different))
        (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.BytesVector

#print axioms InitECandidate.Solver.Input.BytesVector.body_cost
#print axioms InitECandidate.Solver.Input.BytesVector.globals
