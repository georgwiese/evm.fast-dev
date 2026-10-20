import InitECandidate.Solver.Input.OutputProgram

namespace InitECandidate.Solver.Input.Output
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch CounterFlow Flapjack.Compiler.Encoders.Asm

/-- Every output-loop outcome costs at most the actual remaining byte count.
A failed load/shared store stops sooner; host-write success is not assumed. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (word : BitVec 64)
    (lengthBound : length < 2^64)
    (counterCell : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (limitCell : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ length - word.toNat := by
  let counter := ofString "i"
  let limit := ofString "n"
  let body := step
  let code := source.code
  have installed : source.code = code := rfl
  classical
  let invariant := fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    ∃ current : BitVec 64, state.locals.lookup counter = some (.val (.word current)) ∧
      state.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))) ∧ current.toNat ≤ length
  let rank := fun state : PanSemStateFiniteExact 64 Guest.HostMemory => length - (counterWord state counter).toNat
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,
      state.code = code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local counter) (.var .local limit)) = some (.val (.word observed)) →
      observed ≠ 0 → 0 < rank state ∧
        (state.clock ≠ 0 → let output := evaluateHOLFiniteState (decClockHOLFinite state) body
          (output.1 = none ∨ output.1 = some .continue) → invariant output.2 ∧ rank output.2 < rank state) := by
    intro state codeEq valid observed actual nonzero
    obtain ⟨current, currentCell, lengthCell, bounded⟩ := valid
    have lengthMod : length % 18446744073709551616 = length := Nat.mod_eq_of_lt lengthBound
    have read : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local counter) (.var .local limit)) =
        some (.val (.word (if current.toNat < length then 1#64 else 0#64))) := by
      simp [evalHOLFinite, evalHOLExact, toExact, currentCell, lengthCell, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, lengthMod]
    have active : current.toNat < length := by
      by_contra inactive
      rw [if_neg inactive] at read
      have equal : observed = 0#64 := by simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero equal
    have rankEq : rank state = length - current.toNat := by simp [rank, counterWord, currentCell, valueWord]
    refine ⟨by rw [rankEq]; omega, ?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary := step_summary (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1 = none := by
      rcases continuing with normal | continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body = (none, output.2) := Prod.ext normal rfl
    have nextCell := step_advances (decClockHOLFinite state) output.2 current currentCell run
    have nextLimit := (summary.1 normal).trans lengthCell
    have nextNumber : (current + 1#64).toNat = current.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change current.toNat + 1 < 2^64; omega)]
      rfl
    have nextRank : rank output.2 = length - (current.toNat + 1) := by
      simp only [rank, counterWord,counter, nextCell, Option.getD_some, valueWord, nextNumber]
    refine ⟨⟨current + 1#64, nextCell, nextLimit, by rw [nextNumber]; omega⟩, ?_⟩
    rw [nextRank, rankEq]
    omega
  have bounded := ClockCost.ranked_loop code _ step 0 invariant rank (step_cost code) progress source installed
    ⟨word, counterCell, limitCell, initial⟩
  simpa only [rank,counterWord,counterCell,Option.getD_some,valueWord,loop,test,localVar,counter,limit,body,Nat.zero_add,Nat.one_mul] using bounded


/-- The original declaration, loop and return have an all-outcome bound
for the current n parameter, with no memory/host success premises. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length < 2^64)
    (binding : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ length := by
  let ready := QueryBranch.bind source "i" 0#64
  have counter : ready.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have limit : ready.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
    simpa [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using binding
  have loopBound := loop_cost ready length 0#64 small counter limit (by simp)
  have suffix := ClockCost.sequence_current ready loop (.return (.const 0#64)) length 0 (by simpa using loopBound) (ClockCost.returned ready.code _)
  rw [original_shape]
  exact ClockCost.declared_current source "i" (.const 0#64) 0#64 _ length rfl suffix

end InitECandidate.Solver.Input.Output

#print axioms InitECandidate.Solver.Input.Output.loop_cost
#print axioms InitECandidate.Solver.Input.Output.body_cost
