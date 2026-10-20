import InitECandidate.Solver.Input.BytesVectorProgram
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.BytesVector
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem price_sum (bytes chunks depth : Nat) : bytes+72+(115*chunks+55*depth+15)+1=bytes+115*chunks+55*depth+88 := by omega

theorem merkle_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out : BitVec 64) (n : Nat)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) merkleArguments=
      some (Merkle.values cursor (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) out) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,merkleArguments,localVar,packed,output,PackBytes.packedValue,Merkle.values]

/-- The actual packed count is both the real count and limit of the original
vector Merkle call; its mapped buffers follow the same actual packing arena. -/
theorem after_pack_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterPack=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*PackBytes.chunks n+55*depth+15 := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n small arena aligned
  have args := merkle_arguments source cursor out n packed output
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have merkleArena := AllocatedBytes.Arena.weaken _ (832+64*PackBytes.chunks n) (32*max 1 (2*PackBytes.chunks n)) temporaryArena (by omega)
  have front : ∀ result target,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") merkleArguments)=(result,target) →
      result≠some .timeOut → source.clock-target.clock≤115*PackBytes.chunks n+55*depth+14 := by
    intro result target actual notTimeout
    have price := Merkle.call_cost source target cursor (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) (cursor+BitVec.ofNat 64 (PackBytes.padded n))
      out zeros stp accel depth depthSmall (by rw [number]; exact depthBound) (by rw [number]; exact depthBound) workspace.sha heap workspace.zerosLocal
      (by rw [number]; exact packedArena) (by rw [number]; exact merkleArena) temporaryAligned outArena workspace.zeroArena (some none) merkleArguments args result actual notTimeout
    simpa only [number] using price
  have tailPrice : ClockCost.Bound source.code afterMerkle 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code workspace.sha.installed (some none) _) (ClockCost.returned source.code _)
  rw [body_shape.2.2.2] at run
  exact ClockCost.sequence_terminating source post _ afterMerkle (115*PackBytes.chunks n+55*depth+14) 1 front (by
    intro middle normal result target continued notTimeout
    have fields := evaluation_fields source middle _ none normal
    have cost := tailPrice middle fields.2.2.2
    rw [continued] at cost
    exact cost) result run notTimeout

/-- The actual original scoped pack return supplies the vector's real
Merkle arguments/heap/workspace before its reached continuation is priced. -/
theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+55*depth+88 := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n small arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code workspace.sha.installed)
  have calleeWorkspace := SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace
  have calleePrice : ∀ result target,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PackBytes.body=(result,target) → result≠some .timeOut →
      (callEntryStateHOLFinite source callee).clock-target.clock≤n/8+72 := by
    intro result target actual notTimeout
    exact PackBytes.body_cost _ target p cursor n small workspace.sha.installed workspace.sha.domain pLocal nLocal heap inputArena packedArena aligned result actual notTimeout
  have tailPrice : ∀ target returned,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PackBytes.body=(some (.returned returned),target) →
      (shapeEqHOL (shapeOfHOLExact returned) PackBytes.returnShape && shapeEqHOL (shapeOfHOLExact returned) PackBytes.returnShape)=true →
      ∀ result final,evaluateHOLFiniteState (CallNormal.continuationEntry source target "pk" returned) afterPack=(result,final) → result≠some .timeOut →
        target.clock-final.clock≤115*PackBytes.chunks n+55*depth+15 := by
    intro target returned actual checked result final continued notTimeout
    have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n small workspace.sha.installed nLocal heap packedArena returned actual
    have nextWorkspace := SszHash.Workspace.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros calleeWorkspace PackBytes.body (some (.returned returned)) actual
      (fun key different=>PackBytes.globals key source.code workspace.sha.installed different)
    let resumed := CallNormal.continuationEntry source target "pk" returned
    have resumedWorkspace := SszHash.Workspace.of_fields target resumed stp accel chunk zeros nextWorkspace rfl rfl (by intro key different; rfl)
    have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
      (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
    have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
    have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
      change target.globals.lookup (ofString "heap_ptr")=_
      rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
    exact after_pack_cost resumed final cursor out stp accel chunk zeros n depth small depthSmall depthBound resumedWorkspace pk currentOut currentHeap arena aligned outArena result continued notTimeout
  rw [body_shape.2.2.1] at run
  have price := ClockCost.scoped_reached_terminating source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n) PackBytes.body afterPack callee PackBytes.returnShape
    (n/8+72) (115*PackBytes.chunks n+55*depth+15) args called calleePrice tailPrice result run notTimeout
  rw [price_sum] at price
  exact price

end InitECandidate.Solver.Input.BytesVector

#print axioms InitECandidate.Solver.Input.BytesVector.merkle_arguments
#print axioms InitECandidate.Solver.Input.BytesVector.after_pack_cost
#print axioms InitECandidate.Solver.Input.BytesVector.after_mark_cost
