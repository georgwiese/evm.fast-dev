import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A real unsigned counter loop whose limit expression is determined by
one preserved caller binding, such as a decoded tuple field. All outcomes
are covered, without requiring a future successful body or loop. -/
theorem expression_loop_cost (code) (counter key : MlS)
    (binding : ValueHOL 64) (limit : ExpHOL 64) (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length<2^64)
    (limitRead : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.locals.lookup key=some binding → eval current limit=some (.val (.word (BitVec.ofNat 64 length))))
    (priced : ClockCost.Bound code body price) (advance : Advances counter 1 body) (safe : LocalPrefix key body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code=code) (counterCell : source.locals.lookup counter=some (.val (.word word)))
    (keyCell : source.locals.lookup key=some binding) (initial : word.toNat≤length) :
    source.clock-(evaluateHOLFiniteState source (.while (.cmp .lower (.var .local counter) limit) body)).2.clock≤
      (price+1)*(length-word.toNat) := by
  classical
  let invariant := fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ current : BitVec 64,state.locals.lookup counter=some (.val (.word current)) ∧
      state.locals.lookup key=some binding ∧ current.toNat≤length
  let rank := fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>length-(counterWord state counter).toNat
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,state.code=code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address)) (.cmp .lower (.var .local counter) limit)=some (.val (.word observed)) →
      observed≠0 → 0<rank state ∧ (state.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite state) body
        (output.1=none ∨ output.1=some .continue) → invariant output.2 ∧ rank output.2<rank state) := by
    intro state codeEq valid observed actual nonzero
    obtain ⟨current,currentCell,keyCell,bounded⟩ := valid
    have expectedLimit := limitRead state keyCell
    simp only [eval] at expectedLimit
    have lengthMod : length%18446744073709551616=length := Nat.mod_eq_of_lt lengthBound
    have read : evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local counter) limit)=some (.val (.word (if current.toNat<length then 1#64 else 0#64))) := by
      simp [evalHOLFinite,evalHOLExact,toExact,currentCell,expectedLimit,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,
        BitVec.toNat_ofNat,lengthMod]
    have active : current.toNat<length := by
      by_contra inactive
      rw [if_neg inactive] at read
      have zero : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero zero
    have rankEq : rank state=length-current.toNat := by simp [rank,counterWord,currentCell,valueWord]
    refine ⟨by rw [rankEq]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary := safe.summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body=(none,output.2) := Prod.ext normal rfl
    have nextCell := advance (decClockHOLFinite state) output.2 current currentCell run
    have nextKey := (summary.1 normal).trans keyCell
    have nextNumber : (current+1#64).toNat=current.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change current.toNat+1<2^64; omega)]
      rfl
    have nextRank : rank output.2=length-(current.toNat+1) := by
      simp only [rank,counterWord,nextCell,Option.getD_some,valueWord,nextNumber]
    refine ⟨⟨current+1#64,nextCell,nextKey,by rw [nextNumber]; omega⟩,?_⟩
    rw [nextRank,rankEq]
    omega
  have bounded := ClockCost.ranked_loop code _ body price invariant rank priced progress source installed ⟨word,counterCell,keyCell,initial⟩
  simpa only [rank,counterWord,counterCell,Option.getD_some,valueWord] using bounded

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.expression_loop_cost
