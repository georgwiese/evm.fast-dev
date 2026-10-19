import InitECandidate.Solver.GasBudget.StackPushGrowthExecution

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Remove temporary padding from the actual successful growth branch.
Every clock allowance is derived from normal execution. -/
theorem grow_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (positive : 0 < capacity.toNat) (bounded : capacity.toNat ≤ 512)
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word capacity)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (capMapped : source.memaddrs (frame + 232#64))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (arenaAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + ((capacity * 2#64) * 32#64).toNat ≤ scratch.toNat)
    (allocCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (mapped : CopyContext.Mapped source base (growDestination scratch capacity) (32 * capacity.toNat))
    (aligned : CopyGeneral.aligned base (growDestination scratch capacity))
    (normal : evaluateHOLFiniteState source growBranch = (none, target)) :
    capacity.toNat + 2 ≤ source.clock ∧ target = growFinal source frame base scratch capacity := by
  let extra := capacity.toNat + 2
  let padded := {source with clock := source.clock + extra}
  have execution := grow_execute padded frame base scratch memory capacity positive bounded spLocal capLocal ev baseMapped baseCell
    capMapped scratchGlobal memoryGlobal arenaAligned room allocCode copyCode (mapped.of_domain source padded _ _ _ rfl)
    aligned (by change capacity.toNat + 2 ≤ source.clock + extra; dsimp [extra]; omega)
  have lifted := panPropsEvaluateAddClockEq growBranch source none target extra ⟨normal, by intro impossible; cases impossible⟩
  have same := congrArg Prod.snd (lifted.symm.trans execution)
  have price := grow_copy_price base (growDestination scratch capacity) capacity.toNat aligned
  have shifted : growFinal padded frame base scratch capacity =
      {growFinal source frame base scratch capacity with clock := source.clock + extra - 1 -
        (CopyGeneral.cost base (growDestination scratch capacity) (32 * capacity.toNat) + 1)} := by rfl
  have total : source.clock + extra - 1 -
      (CopyGeneral.cost base (growDestination scratch capacity) (32 * capacity.toNat) + 1) = source.clock + extra - extra := by
    rw [price]
    dsimp [extra]
    omega
  rw [shifted, total] at same
  obtain ⟨funded, exactState⟩ := InitECandidate.Solver.strip_full_clock_padding source target
    (growFinal source frame base scratch capacity) extra extra (by omega) same
  have clock : (growFinal source frame base scratch capacity).clock = source.clock - extra := by
    change source.clock - 1 - (CopyGeneral.cost base (growDestination scratch capacity) (32 * capacity.toNat) + 1) = _
    rw [price]
    dsimp [extra]
    omega
  rw [← clock] at exactState
  exact ⟨funded, by simpa using exactState⟩

theorem grow_final_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch capacity query : BitVec 64)
    (notBase : query ≠ frame + 8#64) (notCap : query ≠ frame + 232#64)
    (away : CopyGeneral.Away (growDestination scratch capacity) query (32 * capacity.toNat)) :
    (growFinal source frame base scratch capacity).memory query = source.memory query := by
  change StoreWord.put (StoreWord.put (growCopied source base scratch capacity).memory (frame + 8#64)
    (growDestination scratch capacity)) (frame + 232#64) (capacity * 2#64) query = _
  rw [StoreWord.put, if_neg notCap, StoreWord.put, if_neg notBase]
  exact CopyGeneral.call_memory_away (growReady source scratch capacity) base (growDestination scratch capacity) query (32 * capacity.toNat) away

theorem grow_final_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch capacity : BitVec 64)
    (away : ∀ offset ∈ ([64, 184, 192] : List Nat),
      CopyGeneral.Away (growDestination scratch capacity) (frame + BitVec.ofNat 64 offset) (32 * capacity.toNat)) :
    regularBudget (growFinal source frame base scratch capacity).memory frame = regularBudget source.memory frame ∧
      (growFinal source frame base scratch capacity).memory (frame + 184#64) = source.memory (frame + 184#64) := by
  have cells : ∀ offset ∈ ([64, 184, 192] : List Nat),
      (growFinal source frame base scratch capacity).memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    have cases : offset = 64 ∨ offset = 184 ∨ offset = 192 := by simpa using member
    apply grow_final_away
    · rcases cases with equal | equal | equal <;> subst offset
      all_goals exact offsets_ne frame _ _ (by decide)
    · rcases cases with equal | equal | equal <;> subst offset
      all_goals exact offsets_ne frame _ _ (by decide)
    · exact away offset member
  constructor
  · simp only [regularBudget, wordAt, cells 64 (by simp), cells 184 (by simp), cells 192 (by simp)]
  · exact cells 184 (by simp)

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_normal
#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_final_away
#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_final_budget
