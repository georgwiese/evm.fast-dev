import InitECandidate.Solver.WitnessRadix.MemeqByteReads

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def indexed {F : Type} (state : PanSemStateFiniteExact 64 F) (clock index : Nat) :
    PanSemStateFiniteExact 64 F := bind { state with clock := clock } "i" (BitVec.ofNat 64 index)

def allBlocks (left right : Fin 4 → Fin 8 → BitVec 64) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 => CompareChain.agrees (byteChecks (left (Fin.ofNat 4 start)) (right (Fin.ofNat 4 start))) &&
      allBlocks left right (start + 1) count

def ByteLoopReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → Fin 8 → BitVec 64) : Prop :=
  ∀ start < 4, ∀ clock, ∀ check ∈ byteChecks (left (Fin.ofNat 4 start)) (right (Fin.ofNat 4 start)),
    CompareChain.Ready (indexed state clock (8 * start)) check

theorem indexed_current {F : Type} (state : PanSemStateFiniteExact 64 F) (clock index : Nat) :
    (indexed state clock index).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 index))) := by
  simp [indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem indexed_length {F : Type} (state : PanSemStateFiniteExact 64 F) (clock index : Nat)
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    (indexed state clock index).locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
  have different : ofString "i" ≠ ofString "n" := by decide
  simp [indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, length]

theorem indexed_overwrite {F : Type} (state : PanSemStateFiniteExact 64 F) (clock old next : Nat) :
    bind (indexed state clock old) "i" (BitVec.ofNat 64 next) = indexed state clock next := by
  dsimp only [indexed, QueryBranch.bind, setVarHOLFinite]
  congr 1
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : ofString "i" = name <;> simp [HolFiniteMapExact.update, FUPDATE, same]

private theorem fixed_pair {F Result : Type} (source post : PanSemStateFiniteExact 64 F)
    (result : Result) (clock : post.clock ≤ source.clock) :
    fixClockHOLFinite source (result, post) = (result, post) := by
  have noIncrease : ¬ source.clock < post.clock := by omega
  simp only [fixClockHOLFinite, noIncrease, ↓reduceIte]

/-- Actual byte while loop from any of its four chunk boundaries. The byte
load relation is supplied for the concrete indexed states, not a loop result.
Every execution returns or falls through after at most the remaining chunks. -/
theorem byte_loop_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → Fin 8 → BitVec 64)
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (ready : ByteLoopReady state left right) (remaining start clock : Nat)
    (endAt : start + remaining = 4) (enough : remaining ≤ clock) :
    ∃ paid, paid ≤ remaining ∧
      evaluateHOLFiniteState (indexed state clock (8 * start)) (.while condition8 byteBodies.1) =
        (if allBlocks left right start remaining then none else some (.returned (.val (.word 0#64))),
          if allBlocks left right start remaining then indexed state (clock - paid) 32
          else emptyLocalsHOLFinite { state with clock := clock - paid }) := by
  classical
  induction remaining generalizing start clock with
  | zero =>
      have last : start = 4 := by omega
      subst start
      have test := eval_condition8 (indexed state clock 32) 32#64
        (indexed_current state clock 32) (indexed_length state clock 32 length)
      have stopped : eval (indexed state clock 32) condition8 = some (.val (.word 0#64)) := by
        simpa using test
      refine ⟨0, Nat.le_refl _, ?_⟩
      rw [evaluateHOLFiniteState_while_total]
      simp only [eval, evalHOLFinite] at stopped ⊢
      rw [stopped]
      simp [allBlocks]
  | succ remaining ih =>
      have inside : start < 4 := by omega
      have positive : clock ≠ 0 := by omega
      have indexNat : (BitVec.ofNat 64 (8 * start)).toNat = 8 * start := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have sumNat : (BitVec.ofNat 64 (8 * start) + 8#64).toNat = 8 * start + 8 := by
        rw [BitVec.toNat_add_of_lt (by rw [indexNat]; change 8 * start + 8 < 2 ^ 64; omega), indexNat]
        rfl
      have notLow : ¬ 32#64 < BitVec.ofNat 64 (8 * start) + 8#64 := by
        change ¬ (32 < (BitVec.ofNat 64 (8 * start) + 8#64).toNat)
        rw [sumNat]
        omega
      have test := eval_condition8 (indexed state clock (8 * start)) (BitVec.ofNat 64 (8 * start))
        (indexed_current state clock (8 * start)) (indexed_length state clock (8 * start) length)
      have entering : eval (indexed state clock (8 * start)) condition8 = some (.val (.word 1#64)) := by
        simpa only [notLow, ↓reduceIte] using test
      have decEq : decClockHOLFinite (indexed state clock (8 * start)) =
          indexed state (clock - 1) (8 * start) := rfl
      have bodyRun := byte_body_execute (indexed state (clock - 1) (8 * start))
        (BitVec.ofNat 64 (8 * start)) (left (Fin.ofNat 4 start)) (right (Fin.ofNat 4 start))
        (indexed_current state (clock - 1) (8 * start)) (ready start inside (clock - 1))
      have increment : BitVec.ofNat 64 (8 * start) + 8#64 = BitVec.ofNat 64 (8 * (start + 1)) := by
        have arithmetic : 8 * (start + 1) = 8 * start + 8 := by omega
        rw [arithmetic, BitVec.ofNat_add]
      rw [increment, indexed_overwrite] at bodyRun
      by_cases equal : CompareChain.agrees (byteChecks (left (Fin.ofNat 4 start)) (right (Fin.ofNat 4 start))) = true
      · simp only [equal, ↓reduceIte] at bodyRun
        obtain ⟨paid, bounded, continuation⟩ := ih (start + 1) (clock - 1) (by omega) (by omega)
        refine ⟨paid + 1, by omega, ?_⟩
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval, evalHOLFinite] at entering ⊢
        rw [entering]
        simp only [show (1#64) ≠ 0#64 by decide, ↓reduceIte]
        change (if clock = 0 then _ else _) = _
        rw [if_neg positive, decEq, bodyRun]
        rw [fixed_pair (indexed state (clock - 1) (8 * start))
          (indexed state (clock - 1) (8 * (start + 1)))
          (none : Option (PanSemResultExact 64)) (Nat.le_refl _)]
        simp only [allBlocks, equal, Bool.true_and]
        have subtract : clock - (paid + 1) = clock - 1 - paid := by omega
        simpa only [subtract] using continuation
      · have unequal : CompareChain.agrees (byteChecks (left (Fin.ofNat 4 start)) (right (Fin.ofNat 4 start))) = false :=
          Bool.eq_false_iff.mpr equal
        simp only [unequal, Bool.false_eq_true, ↓reduceIte] at bodyRun
        refine ⟨1, by omega, ?_⟩
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval, evalHOLFinite] at entering ⊢
        rw [entering]
        simp only [show (1#64) ≠ 0#64 by decide, ↓reduceIte]
        change (if clock = 0 then _ else _) = _
        rw [if_neg positive, decEq, bodyRun]
        rw [fixed_pair (indexed state (clock - 1) (8 * start))
          (emptyLocalsHOLFinite (indexed state (clock - 1) (8 * start)))
          (some (.returned (.val (.word 0#64))) : Option (PanSemResultExact 64)) (Nat.le_refl _)]
        simp [allBlocks, unequal, indexed, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byte_loop_execute
