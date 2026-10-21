import InitECandidate.Solver.Input.BytesListSuffixCost
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.BytesListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem price_sum (bytes chunks : Nat) : bytes+72+(115*chunks+74)+1=bytes+115*chunks+147 := by omega

/-- Actual scoped pack execution supplies the extra-data hash's real tuple,
heap and initialized workspace; the declared limit remains the actual1. -/
theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+147 := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code workspace.sha.installed)
  have calleeWorkspace := SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace
  have calleePrice : ∀ result target,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PackBytes.body=(result,target) → result≠some .timeOut →
      (callEntryStateHOLFinite source callee).clock-target.clock≤n/8+72 := by
    intro result target actual notTimeout
    exact PackBytes.body_cost _ target p cursor n (by omega) workspace.sha.installed workspace.sha.domain pLocal nLocal heap inputArena packedArena aligned result actual notTimeout
  have tailPrice : ∀ target returned,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PackBytes.body=(some (.returned returned),target) →
      (shapeEqHOL (shapeOfHOLExact returned) PackBytes.returnShape && shapeEqHOL (shapeOfHOLExact returned) PackBytes.returnShape)=true →
      ∀ result final,evaluateHOLFiniteState (CallNormal.continuationEntry source target "pk" returned) afterPack=(result,final) → result≠some .timeOut →
        target.clock-final.clock≤115*PackBytes.chunks n+74 := by
    intro target returned actual checked result final continued notTimeout
    have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n (by omega) workspace.sha.installed nLocal heap packedArena returned actual
    have nextWorkspace := SszHash.Workspace.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros calleeWorkspace PackBytes.body (some (.returned returned)) actual
      (fun key different=>PackBytes.globals key source.code workspace.sha.installed different)
    let resumed := CallNormal.continuationEntry source target "pk" returned
    have resumedWorkspace := SszHash.Workspace.of_fields target resumed stp accel chunk zeros nextWorkspace rfl rfl (by intro key different; rfl)
    have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
      (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
    have currentN := (CallNormal.continuation_lookup_other source target "pk" "n" returned (by decide)).trans count
    have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
    have currentLimit := (CallNormal.continuation_lookup_other source target "pk" "limit_chunks" returned (by decide)).trans limitLocal
    have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
      change target.globals.lookup (ofString "heap_ptr")=_
      rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
    exact after_pack_cost resumed final cursor out stp accel chunk zeros n short resumedWorkspace pk currentLimit currentOut currentN currentHeap arena aligned outArena result continued notTimeout
  rw [body_shape.2.1] at run
  have price := ClockCost.scoped_reached_terminating source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n) PackBytes.body afterPack callee PackBytes.returnShape
    (n/8+72) (115*PackBytes.chunks n+74) args called calleePrice tailPrice result run notTimeout
  rw [price_sum] at price
  exact price

end InitECandidate.Solver.Input.BytesListHash

#print axioms InitECandidate.Solver.Input.BytesListHash.after_mark_cost
