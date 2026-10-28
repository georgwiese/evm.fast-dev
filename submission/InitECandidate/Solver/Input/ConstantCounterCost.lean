import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Signed constant-limit loops in the original SHA helpers. The actual
counter stays below the signed boundary; every abnormal body outcome is
covered and continuing iterations derive their next counter from execution. -/
theorem constant_loop_cost (code) (counter marker : MlS) (body : ProgHOL 64) (price length : Nat)
    (small : length<2^63) (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalPrefix marker body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code=code) (cell : source.locals.lookup counter=some (.val (.word word))) (initial : word.toNat≤length) :
    source.clock-(evaluateHOLFiniteState source (.while (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length))) body)).2.clock≤
      (price+1)*(length-word.toNat) := by
  classical
  let invariant := fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ current : BitVec 64,state.locals.lookup counter=some (.val (.word current)) ∧ current.toNat≤length
  let rank := fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>length-(counterWord state counter).toNat
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,state.code=code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=some (.val (.word observed)) → observed≠0 →
      0<rank state ∧ (state.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite state) body
        (output.1=none ∨ output.1=some .continue) → invariant output.2 ∧ rank output.2<rank state) := by
    intro state codeEq valid observed actual nonzero
    obtain ⟨current,currentCell,currentBound⟩ := valid
    have lengthNumber : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have currentSmall : current.toNat<9223372036854775808 := by omega
    have lengthSmall : length<9223372036854775808 := small
    have read : evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=
        some (.val (.word (if current.toNat<length then 1#64 else 0#64))) := by
      simp [evalHOLFinite,evalHOLExact,toExact,currentCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,lengthNumber,currentSmall,lengthSmall]
    have active : current.toNat<length := by
      apply Classical.byContradiction
      intro inactive
      rw [if_neg inactive] at read
      have zero : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero zero
    have rankEq : rank state=length-current.toNat := by simp [rank,counterWord,currentCell,valueWord]
    refine ⟨by rw [rankEq]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary := safe.summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body=(none,output.2) := Prod.ext normal rfl
    have nextCell := advance (decClockHOLFinite state) output.2 current currentCell run
    have nextNumber : (current+1#64).toNat=current.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change current.toNat+1<2^64; omega)]
      rfl
    have nextRank : rank output.2=length-(current.toNat+1) := by simp only [rank,counterWord,nextCell,Option.getD_some,valueWord,nextNumber]
    exact ⟨⟨current+1#64,nextCell,by rw [nextNumber]; omega⟩,by rw [nextRank,rankEq]; omega⟩
  have cost := ClockCost.ranked_loop code _ body price invariant rank priced progress source installed ⟨word,cell,initial⟩
  simpa only [rank,counterWord,cell,Option.getD_some,valueWord] using cost

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.constant_loop_cost
