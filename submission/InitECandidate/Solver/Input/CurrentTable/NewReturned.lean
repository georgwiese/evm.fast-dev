import InitECandidate.Solver.Input.CurrentTable.NewCompleteCost

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def finishSource (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) :=
  finishStored (finalEntry source heap cap) heap cap

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- An enclosing normal return must pass all four actual allocations and
metadata stores. It derives each array's room, the real table value and
exact canonical nonlocal result; a cheap stopped alternative cannot be
substituted for this actual returned state. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ 4≤source.clock ∧ heap.toNat+88≤2952790016 ∧
      (keysPointer heap).toNat+(size32 cap).toNat≤2952790016 ∧
      (nodesPointer heap cap).toNat+(size32 cap).toNat≤2952790016 ∧
      (orderPointer heap cap).toNat+(size8 cap).toNat≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      LocalEffects.erase post=LocalEffects.erase (finishSource source heap cap) ∧ post.clock=source.clock-4 := by
  rcases final_trace source post heap cap keyLocal capLocal atLeastTwo heapCell heapLower heapBound heapAligned domain installed (some (.returned value)) run with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,firstRoom,keysRoom,nodesRoom,orderRoom,arena,inner,continued,endpoint⟩:=reached
    obtain ⟨tableCell,ncapCell⟩:=final_cells source heap cap keyLocal capLocal
    have finish:=final_fields_execute (finalEntry source heap cap) heap cap domain arena heapAligned tableCell ncapCell
    rw [finish] at continued
    have answer : value=.val (.word heap) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst continued).symm
    have innerEq:=congrArg Prod.snd continued
    dsimp only at innerEq
    refine ⟨answer,funded,firstRoom,keysRoom,nodesRoom,orderRoom,arena,?_,?_⟩
    · rw [endpoint,←innerEq]
      rfl
    · rw [endpoint,←innerEq]
      change source.clock-1-1-1-1=source.clock-4
      omega

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.body_returned
