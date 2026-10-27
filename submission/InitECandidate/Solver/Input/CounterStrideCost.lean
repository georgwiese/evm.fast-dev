import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

/-- Unsigned variable-limit loops with an actual positive stride. The last
iteration may overshoot the limit; the ceiling quotient counts it once.
Only real continuations must preserve the limit and advance the counter. -/
theorem unsigned_stride_cost (code) (counter limit : MlS) (body : ProgHOL 64)
    (price stride length : Nat) (positive : 0 < stride)
    (small : length + stride < 2^64)
    (priced : ClockCost.Bound code body price) (advance : Advances counter stride body)
    (safe : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory, LocalSummary limit body state)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length + stride - 1) :
    source.clock - (evaluateHOLFiniteState source
      (.while (.cmp .lower (.var .local counter) (.var .local limit)) body)).2.clock ≤
      (price + 1) * ((length + stride - 1 - word.toNat) / stride) := by
  classical
  let invariant := fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    ∃ current : BitVec 64, state.locals.lookup counter = some (.val (.word current)) ∧
      state.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))) ∧
      current.toNat ≤ length + stride - 1
  let rank := fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    (length + stride - 1 - (counterWord state counter).toNat) / stride
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,
      state.code = code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local counter) (.var .local limit)) = some (.val (.word observed)) →
      observed ≠ 0 → 0 < rank state ∧
        (state.clock ≠ 0 → let output := evaluateHOLFiniteState (decClockHOLFinite state) body
          (output.1 = none ∨ output.1 = some .continue) →
            invariant output.2 ∧ rank output.2 < rank state) := by
    intro state codeEq valid observed actual nonzero
    obtain ⟨current, currentCell, lengthCell, bounded⟩ := valid
    have lengthSmall : length < 2^64 := by omega
    have strideSmall : stride < 2^64 := by omega
    have number : (BitVec.ofNat 64 length).toNat = length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall]
    have read : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local counter) (.var .local limit)) =
        some (.val (.word (if current.toNat < length then 1#64 else 0#64))) := by
      simp [evalHOLFinite, evalHOLExact, toExact, currentCell, lengthCell, wordCmpHOL,
        BitVec.lt_def, number]
    have active : current.toNat < length := by
      by_cases active : current.toNat < length
      · exact active
      · rw [if_neg active] at read
        have equal : observed = 0#64 := by
          simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using actual.symm.trans read
        exact (nonzero equal).elim
    have before : rank state = (length + stride - 1 - current.toNat) / stride := by
      simp [rank, counterWord, currentCell, valueWord]
    refine ⟨by rw [before]; exact Nat.div_pos (by omega) positive, ?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary := safe (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1 = none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body = (none, output.2) := Prod.ext normal rfl
    have nextCell := advance (decClockHOLFinite state) output.2 current currentCell run
    have nextLimit := (summary.1 normal).trans lengthCell
    have nextNumber : (current + BitVec.ofNat 64 stride).toNat = current.toNat + stride := by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt strideSmall]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt strideSmall]
    have after : rank output.2 = (length + stride - 1 - (current.toNat + stride)) / stride := by
      simp [rank, counterWord, nextCell, valueWord, nextNumber]
    have difference : length + stride - 1 - current.toNat =
        (length + stride - 1 - (current.toNat + stride)) + stride := by omega
    refine ⟨⟨current + BitVec.ofNat 64 stride, nextCell, nextLimit, by rw [nextNumber]; omega⟩, ?_⟩
    rw [after, before, difference, Nat.add_div_right _ positive]
    omega
  have cost := ClockCost.ranked_loop code _ body price invariant rank priced progress source installed
    ⟨word, counterCell, limitCell, initial⟩
  simpa only [rank, counterWord, counterCell, Option.getD_some, valueWord] using cost

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.unsigned_stride_cost
