import InitECandidate.Solver.GasBudget.StackPushGrowthBodyEntry
import InitECandidate.Solver.GasBudget.StackPushWrites

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Complete successful original stack_push when the full stack doubles.
All source clocks and reached stores are derived from actual normal execution.
Current ownership of the copied region and the new tuple slot is explicit. -/
theorem growth_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (view : GrowthView source frame base scratch memory capacity) (storedValue returned : ValueHOL 64)
    (vLocal : source.locals.lookup (ofString "v") = some storedValue)
    (valueShape : shapeOfHOLExact storedValue = .comb [.one, .one, .one, .one])
    (copyApart : ∀ offset ∈ ([64, 184, 192] : List Nat),
      CopyGeneral.Away (growDestination scratch capacity) (frame + BitVec.ofNat 64 offset) (32 * capacity.toNat))
    (slotApart : ∀ offset ∈ ([8, 64, 184, 192, 232] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index))
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ capacity.toNat + 2 ≤ source.clock ∧
      post.clock = source.clock - (capacity.toNat + 2) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite
        {Arenas.post source .down scratch ((capacity * 2#64) * 32#64) with memory := post.memory, clock := post.clock} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 16#64) = .word (capacity + 1#64) ∧
      (wordAt post.memory (frame + 16#64)).toNat = capacity.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ (capacity * 2#64).toNat ∧
      post.memory (frame + 8#64) = .word (growDestination scratch capacity) ∧
      post.memory (frame + 232#64) = .word (capacity * 2#64) ∧
      (∀ address, address ≠ frame + 16#64 → address ≠ frame + 8#64 → address ≠ frame + 232#64 →
        CopyGeneral.Away (growDestination scratch capacity) address (32 * capacity.toNat) →
        (∀ index < 4, address ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index)) →
        post.memory address = source.memory address) := by
  obtain ⟨inner, funded, spMapped, capMapped, writesRun, postEq⟩ :=
    growth_body_entry source post frame base scratch memory capacity view returned normal
  let entry := entered source capacity capacity
  let ready := growFinal entry frame base scratch capacity
  have readyEV : ready.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [ready, entry, entered, growFinal, growCopied, CopyGeneral.callState, growReady, Arenas.post, Arenas.pointerName,
      QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using view.ev
  have readySP : ready.locals.lookup (ofString "sp") = some (.val (.word capacity)) :=
    (bind_lookup_other _ "cap" "sp" _ (by decide)).trans (bind_lookup_same _ _ _)
  have readyV : ready.locals.lookup (ofString "v") = some storedValue :=
    (bind_lookup_other _ "cap" "v" _ (by decide)).trans ((bind_lookup_other _ "sp" "v" _ (by decide)).trans vLocal)
  have baseCell : ready.memory (frame + 8#64) = .word (growDestination scratch capacity) := by
    change StoreWord.put (StoreWord.put _ (frame + 8#64) (growDestination scratch capacity)) (frame + 232#64) _ (frame + 8#64) = _
    rw [StoreWord.put, if_neg (offsets_ne frame 8#64 232#64 (by decide))]
    simp [StoreWord.put]
  obtain ⟨zero, clock, fields, spFinal, outside⟩ := writes_normal ready inner frame (growDestination scratch capacity) capacity
    storedValue returned readyEV readySP readyV valueShape view.baseMapped baseCell writesRun
  have postMemory : post.memory = inner.memory := by rw [postEq]; rfl
  have postClock : post.clock = source.clock - (capacity.toNat + 2) := by
    rw [postEq]
    change inner.clock = _
    rw [clock]
    change source.clock - 1 - (CopyGeneral.cost base (growDestination scratch capacity) (32 * capacity.toNat) + 1) = _
    rw [grow_copy_price base (growDestination scratch capacity) capacity.toNat view.aligned]
    omega
  have canonical : emptyLocalsHOLFinite post = emptyLocalsHOLFinite
      {Arenas.post source .down scratch ((capacity * 2#64) * 32#64) with memory := post.memory, clock := post.clock} := by
    rw [postEq]
    have exactFields := fields
    change emptyLocalsHOLFinite inner = emptyLocalsHOLFinite {ready with memory := inner.memory} at exactFields
    have restoreFields : emptyLocalsHOLFinite (restore source "sp" (restore (bind source "sp" capacity) "cap" inner)) = emptyLocalsHOLFinite inner := rfl
    rw [restoreFields]
    change emptyLocalsHOLFinite inner = emptyLocalsHOLFinite
      {Arenas.post source .down scratch ((capacity * 2#64) * 32#64) with memory := inner.memory, clock := inner.clock}
    rw [clock]
    exact exactFields
  have retained (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :
      post.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    rw [postMemory]
    have next := outside (frame + BitVec.ofNat 64 offset) (by
      apply offsets_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide) (slotApart offset (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        tauto))
    exact next.trans (grow_final_away entry frame base scratch capacity _
      (by apply offsets_ne; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide)
      (by apply offsets_ne; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide)
      (copyApart offset member))
  have finalSP : post.memory (frame + 16#64) = .word (capacity + 1#64) := by rw [postMemory]; exact spFinal
  have fits : capacity.toNat + (1#64 : BitVec 64).toNat < 2 ^ 64 := by have bound := view.bounded; change capacity.toNat + 1 < 2 ^ 64; omega
  have naturalSP : (wordAt post.memory (frame + 16#64)).toNat = capacity.toNat + 1 := by
    simp [wordAt, finalSP, MemoryBytes.wordBits, BitVec.toNat_add_of_lt fits]
  obtain ⟨doubled, more, capBound, allocation, copied⟩ := grow_numbers capacity view.positive view.bounded
  have finalBase : post.memory (frame + 8#64) = .word (growDestination scratch capacity) := by
    rw [postMemory]
    exact (outside _ (offsets_ne frame 8#64 16#64 (by decide)) (slotApart 8 (by simp))).trans baseCell
  have finalCap : post.memory (frame + 232#64) = .word (capacity * 2#64) := by
    rw [postMemory]
    have cell : ready.memory (frame + 232#64) = .word (capacity * 2#64) := by
      change StoreWord.put _ (frame + 232#64) (capacity * 2#64) (frame + 232#64) = _
      simp [StoreWord.put]
    exact (outside _ (offsets_ne frame 232#64 16#64 (by decide)) (slotApart 232 (by simp))).trans cell
  refine ⟨zero, funded, postClock, canonical, ?_, retained 184 (by simp), finalSP, naturalSP, by omega, finalBase, finalCap, ?_⟩
  · simp only [regularBudget, wordAt, retained 64 (by simp), retained 184 (by simp), retained 192 (by simp)]
  · intro address notSP notBase notCap away notSlot
    rw [postMemory]
    exact (outside address notSP notSlot).trans (grow_final_away entry frame base scratch capacity address notBase notCap away)

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_body_normal
