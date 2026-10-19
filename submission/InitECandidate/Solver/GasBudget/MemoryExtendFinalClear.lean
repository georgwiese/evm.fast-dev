import InitECandidate.Solver.GasBudget.MemoryExtendGrowthClear
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The length update runs after capacity has already been installed, so its
current ownership does not require the old length/capacity slack relation. -/
structure ClearView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base scratch : BitVec 64) : Prop where
  installed : Input.OriginalCode.Installed source.code
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  baseMapped : source.memaddrs (frame + 24#64)
  lengthMapped : source.memaddrs (frame + 32#64)
  baseCell : source.memory (frame + 24#64) = .word base
  arena : FrameNew.ArenaMapped source base scratch

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem final_clear_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base scratch length expand : BitVec 64) (returned : ValueHOL 64)
    (view : ClearView source frame base scratch)
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word length)))
    (expandLocal : source.locals.lookup (ofString "expand_by") = some (.val (.word expand)))
    (nextLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))))
    (lower : base.toNat ≤ (base + length).toNat)
    (upper : (base + length).toNat + expand.toNat ≤ scratch.toNat)
    (aligned : (base + length).toNat % 8 = 0)
    (expandAligned : expand.toNat % 32 = 0)
    (expandSmall : expand.toNat + 32 < 2 ^ 64)
    (normal : evaluateHOLFiniteState source afterGrowth = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ expand.toNat / 32 + 1 ≤ source.clock ∧
      post = emptyLocalsHOLFinite {source with
        memory := StoreWord.put (Zero.finalMemory source.memory (base + length) expand.toNat)
          (frame + 32#64) (newLength length expand)
        clock := source.clock - (expand.toNat / 32 + 1)} ∧
      post.memory (frame + 32#64) = .word (newLength length expand) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → post.memory query = source.memory query) := by
  let clear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero")
    [.op .add [frameLoad 24#64, localVar "len"], localVar "expand_by"]
  let finish : ProgHOL 64 := .seq (.store (frameAddress 32#64) (localVar "nlen")) returnZero
  have safe : Input.LocalPrefix (ofString "nlen") clear := .call none _ _ (by simp)
  obtain ⟨cleared, clearRun, finishRun, retained⟩ := safe.normal_continue source post finish returned normal
  have baseRead := frame_read source frame 24#64 base view.ev view.baseMapped view.baseCell
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [.op .add [frameLoad 24#64, localVar "len"], localVar "expand_by"] = some (Zero.values (base + length) expand.toNat) := by
    simp only [eval] at baseRead
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, baseRead, localVar, lengthLocal, expandLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp, Zero.values, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have multiple : expand.toNat % 8 = 0 := by have division := Nat.mod_add_div expand.toNat 32; omega
  obtain ⟨fits, clearedEq⟩ := Zero.call_normal source cleared _ (base + length) expand.toNat args
    (zero_code source.code view.installed) expandSmall multiple aligned
    (FrameNew.arena_mapped_subregion source base scratch (base + length) expand.toNat view.arena lower upper aligned) clearRun
  have clearedEV : cleared.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [clearedEq]; exact view.ev
  have clearedNext : cleared.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))) := retained.trans nextLocal
  have mapped : cleared.memaddrs (frame + 32#64) := by rw [clearedEq]; exact view.lengthMapped
  let stored := {cleared with memory := StoreWord.put cleared.memory (frame + 32#64) (newLength length expand)}
  have storeRun := StoreWord.execute cleared (frameAddress 32#64) (localVar "nlen") (frame + 32#64) (newLength length expand)
    (address_read cleared frame 32#64 clearedEV) (by simp [eval, localVar, evalHOLExact, toExact, clearedNext]) mapped
  change evaluateHOLFiniteState cleared (.seq (.store (frameAddress 32#64) (localVar "nlen")) returnZero) = _ at finishRun
  rw [StateSteps.next_sequence cleared stored _ returnZero storeRun (Nat.le_refl _)] at finishRun
  obtain ⟨read, postEq⟩ := Input.return_normal stored post (.const 0#64) returned finishRun
  have value : returned = .val (.word 0#64) := by simpa [eval, evalHOLExact] using (Option.some.inj read).symm
  have price : Zero.price expand.toNat = expand.toNat / 32 := by simp [Zero.price, expandAligned]
  change Zero.price expand.toNat + 1 ≤ source.clock at fits
  rw [price] at fits
  have finalEq : post = emptyLocalsHOLFinite {source with
      memory := StoreWord.put (Zero.finalMemory source.memory (base + length) expand.toNat) (frame + 32#64) (newLength length expand)
      clock := source.clock - (expand.toNat / 32 + 1)} := by
    rw [postEq]
    dsimp only [stored]
    rw [clearedEq, price]
  refine ⟨value, fits, finalEq, ?_, ?_⟩
  · rw [finalEq]
    simp [emptyLocalsHOLFinite, StoreWord.put]
  · intro query outside other
    rw [finalEq]
    change StoreWord.put _ (frame + 32#64) _ query = _
    rw [StoreWord.put, if_neg other]
    exact zero_away source.memory base scratch (base + length) query expand.toNat lower upper outside

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.final_clear_normal
