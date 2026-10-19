import InitECandidate.Solver.GasBudget.StackPushGrowthOwnership
import InitECandidate.Solver.GasBudget.FrameRank

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual growing push preserves all physical live gas accounting.
The copy/tuple footprint is discharged by current arena ownership. -/
theorem growth_call_sums (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (view : GrowthView source frame base scratch memory capacity) (arguments : List (ExpHOL 64))
    (code : source.code.lookup (ofString "stack_push") = some (formals, body, .one))
    (headerOwned : ∀ offset ∈ ([8, 64, 184, 192, 232] : List Nat),
      Arenas.Outside memory scratch (frame + BitVec.ofNat 64 offset))
    (ancestors : List (BitVec 64))
    (ancestorOwned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      Arenas.Outside memory scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 16#64 ∧
      ancestor + BitVec.ofNat 64 offset ≠ frame + 8#64 ∧
      ancestor + BitVec.ofNat 64 offset ≠ frame + 232#64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "stack_push") arguments) = (none, target)) :
    capacity.toNat + 3 ≤ source.clock ∧ target.clock = source.clock - (capacity.toNat + 3) ∧
      FrameSums.budget target.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used target.memory (frame :: ancestors) = FrameSums.used source.memory (frame :: ancestors) ∧
      source.clock - target.clock + capacity.toNat = 3 + (wordAt target.memory (frame + 232#64)).toNat ∧
      target.memory (frame + 8#64) = .word (growDestination scratch capacity) ∧
      target.memory (frame + 232#64) = .word (capacity * 2#64) ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ (wordAt target.memory (frame + 232#64)).toNat := by
  have copyApart : ∀ offset ∈ ([64, 184, 192] : List Nat),
      CopyGeneral.Away (growDestination scratch capacity) (frame + BitVec.ofNat 64 offset) (32 * capacity.toNat) := by
    intro offset member
    apply view.copy_away
    apply headerOwned
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have slotApart : ∀ offset ∈ ([8, 64, 184, 192, 232] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index) := by
    intro offset member index inside
    exact view.slot_away _ (headerOwned offset member) index inside
  obtain ⟨funded, clock, canonical, parentBudget, parentUsed, spFinal, naturalSP, depth, baseFinal, capFinal, outside⟩ :=
    growth_call_normal source target frame base scratch memory capacity view arguments code copyApart slotApart normal
  have ancestorCells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      target.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    obtain ⟨notSP, notBase, notCap⟩ := apart ancestor member offset inside
    exact outside _ notSP notBase notCap (view.copy_away _ (ancestorOwned ancestor member offset inside))
      (fun index bound => view.slot_away _ (ancestorOwned ancestor member offset inside) index bound)
  have ancestorBudget := FrameSums.budget_congr source.memory target.memory ancestors ancestorCells
  have ancestorUsed := FrameSums.used_congr source.memory target.memory ancestors
    (by intro ancestor member; exact ancestorCells ancestor member 184 (by simp))
  have doubled := (grow_numbers capacity view.positive view.bounded).1
  have capNumber : (wordAt target.memory (frame + 232#64)).toNat = 2 * capacity.toNat := by
    simpa only [wordAt, capFinal, MemoryBytes.wordBits] using doubled
  refine ⟨funded, clock, ?_, ?_, ?_, baseFinal, capFinal, ?_⟩
  · change regularBudget target.memory frame + FrameSums.budget target.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [parentBudget, ancestorBudget]
  · change (wordAt target.memory (frame + 184#64)).toNat + FrameSums.used target.memory ancestors =
      (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors
    simp only [wordAt, parentUsed, ancestorUsed]
  · rw [capNumber, clock]
    omega
  · simpa only [wordAt, capFinal, MemoryBytes.wordBits] using depth

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_call_sums
