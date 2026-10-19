import InitECandidate.Solver.GasBudget.MemoryExtendGeometry
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem View.after_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64} (view : View source frame base length capacity pointer scratch)
    (fields : Input.LocalEffects.erase target = Input.LocalEffects.erase source) : View target frame base length capacity pointer scratch := by
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := source.clock}) fields
  change {target with locals := source.locals, clock := source.clock} = source at reset
  rw [← reset] at view
  cases view
  constructor <;> assumption

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Actual growing-buffer allocation, capacity clear and header store. Room
and source-clock funding are derived from the real normal calls. The old
length remains until the subsequent expansion clear/store. -/
theorem grow_tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat)
    (view : View source frame base length capacity pointer scratch) (advance : MemoryExpansionCost.Advance length expand amount used)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (ncapLocal : source.locals.lookup (ofString "ncap") = some (.val (.word (nextCapacity length capacity expand))))
    (normal : evaluateHOLFiniteState source growTail = (none, post)) :
    (nextCapacity length capacity expand - capacity).toNat / 32 + 2 ≤ source.clock ∧
      post = {Arenas.post source .up pointer (nextCapacity length capacity expand - capacity) with
        memory := StoreWord.put (Zero.finalMemory source.memory (base + capacity) (nextCapacity length capacity expand - capacity).toNat)
          (frame + 40#64) (nextCapacity length capacity expand)
        clock := source.clock - ((nextCapacity length capacity expand - capacity).toNat / 32 + 2)} ∧
      Geometry base length capacity pointer scratch expand ∧
      post.memory (frame + 40#64) = .word (nextCapacity length capacity expand) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  obtain ⟨allocated, allocRun, restRun⟩ := Input.sequence_none source post allocate (.seq growthClear (.store (frameAddress 40#64) (localVar "ncap"))) normal
  let delta := nextCapacity length capacity expand - capacity
  have allocArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [capacityDifference] = some [.val (.word delta)] := by
    simp [capacityDifference, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, capLocal, ncapLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp, delta]
  obtain ⟨room, allocFits, allocatedEq⟩ := Arenas.ignored_normal source allocated .up pointer scratch delta [capacityDifference] allocArgs
    (alloc_code .up source.code view.installed) (trap_code source.code view.installed) view.pointerGlobal view.scratchGlobal view.ordered view.scratchAligned allocRun
  have region := geometry source frame base length capacity pointer scratch expand amount view used advance room
  obtain ⟨cleared, clearRun, storeRun⟩ := Input.sequence_none allocated post growthClear (.store (frameAddress 40#64) (localVar "ncap")) restRun
  have allocatedEV : allocated.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    rw [allocatedEq]
    simpa [Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, ofString] using view.ev
  have allocatedCap : allocated.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [allocatedEq]; exact capLocal
  have allocatedNCap : allocated.locals.lookup (ofString "ncap") = some (.val (.word (nextCapacity length capacity expand))) := by rw [allocatedEq]; exact ncapLocal
  have allocatedBaseMapped : allocated.memaddrs (frame + 24#64) := by rw [allocatedEq]; exact view.mapped 24 (by simp)
  have allocatedBaseCell : allocated.memory (frame + 24#64) = .word base := by rw [allocatedEq]; exact view.baseCell
  have baseRead := frame_read allocated frame 24#64 base allocatedEV allocatedBaseMapped allocatedBaseCell
  have zeroArgs : evalListHOLFinite allocated (h := fun address => Classical.propDecidable (allocated.memaddrs address))
      [.op .add [frameLoad 24#64, localVar "cap"], capacityDifference] = some (Zero.values (base + capacity) delta.toNat) := by
    simp only [eval] at baseRead
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, baseRead, capacityDifference, localVar, allocatedCap, allocatedNCap,
      valueIsWord, valueWord, wordOpHOL, wordOp, Zero.values, BitVec.ofNat_toNat, BitVec.setWidth_eq, delta]
    change nextCapacity length capacity expand - capacity = BitVec.ofNat 64 ((nextCapacity length capacity expand - capacity).toNat)
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have allocatedInstalled : Input.OriginalCode.Installed allocated.code := by rw [allocatedEq]; exact view.installed
  have lower : base.toNat ≤ (base + capacity).toNat := by rw [← region.oldPointer]; have cursor := view.cursor; omega
  have upper : (base + capacity).toNat + delta.toNat ≤ scratch.toNat := by rw [← region.oldPointer]; exact room
  have mappedArena : FrameNew.ArenaMapped allocated base scratch := by rw [allocatedEq]; exact view.arena
  have aligned : (base + capacity).toNat % 8 = 0 := by rw [← region.oldPointer]; exact region.pointerAligned
  have deltaAligned : delta.toNat % 32 = 0 := region.deltaAligned
  have deltaMultiple : delta.toNat % 8 = 0 := by have division := Nat.mod_add_div delta.toNat 32; omega
  have deltaSmall : delta.toNat + 32 < 2 ^ 64 := by
    have difference := region.deltaNat
    have capBound := region.nextSlack
    have lenBound := advance.byteBound
    change (newLength length expand).toNat ≤ 178956960 at lenBound
    change delta.toNat = (nextCapacity length capacity expand).toNat - capacity.toNat at difference
    omega
  obtain ⟨zeroFits, clearedEq⟩ := Zero.call_normal allocated cleared _ (base + capacity) delta.toNat zeroArgs
    (zero_code allocated.code allocatedInstalled) deltaSmall deltaMultiple aligned
    (FrameNew.arena_mapped_subregion allocated base scratch (base + capacity) delta.toNat mappedArena lower upper aligned) clearRun
  have clearedEV : cleared.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [clearedEq]; exact allocatedEV
  have clearedNCap : cleared.locals.lookup (ofString "ncap") = some (.val (.word (nextCapacity length capacity expand))) := by rw [clearedEq]; exact allocatedNCap
  have capMapped : cleared.memaddrs (frame + 40#64) := by rw [clearedEq, allocatedEq]; exact view.mapped 40 (by simp)
  have stored := StoreWord.execute cleared (frameAddress 40#64) (localVar "ncap") (frame + 40#64) (nextCapacity length capacity expand)
    (address_read cleared frame 40#64 clearedEV) (by simp [eval, localVar, evalHOLExact, toExact, clearedNCap]) capMapped
  have postEq := congrArg Prod.snd (storeRun.symm.trans stored)
  change post = {cleared with memory := StoreWord.put cleared.memory (frame + 40#64) (nextCapacity length capacity expand)} at postEq
  rw [clearedEq, allocatedEq] at postEq
  have price : Zero.price delta.toNat = delta.toNat / 32 := by simp [Zero.price, deltaAligned]
  change Zero.price delta.toNat + 1 ≤ allocated.clock at zeroFits
  rw [allocatedEq] at zeroFits
  change Zero.price delta.toNat + 1 ≤ source.clock - 1 at zeroFits
  have funded : delta.toNat / 32 + 2 ≤ source.clock := by rw [price] at zeroFits; omega
  have spent : source.clock - 1 - (Zero.price delta.toNat + 1) = source.clock - (delta.toNat / 32 + 2) := by rw [price]; omega
  change post = {Arenas.post source .up pointer delta with
    memory := StoreWord.put (Zero.finalMemory source.memory (base + capacity) delta.toNat) (frame + 40#64) (nextCapacity length capacity expand)
    clock := source.clock - 1 - (Zero.price delta.toNat + 1)} at postEq
  rw [spent] at postEq
  refine ⟨funded, postEq, region, ?_, ?_⟩
  · rw [postEq]
    change StoreWord.put _ (frame + 40#64) _ (frame + 40#64) = _
    simp [StoreWord.put]
  · intro query outside notCapacity
    rw [postEq]
    change StoreWord.put _ (frame + 40#64) _ query = _
    rw [StoreWord.put, if_neg notCapacity]
    exact zero_away source.memory base scratch (base + capacity) query delta.toNat lower upper outside

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_erase
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.grow_tail_normal
