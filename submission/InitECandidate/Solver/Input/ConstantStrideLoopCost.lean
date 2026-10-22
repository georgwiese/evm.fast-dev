import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.Input.ByteStoreLocal

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

/-- Signed constant-limit loops with an actual aligned strided counter.
Normal bodies derive each increment; aborted reads/stores need no future
invariant. The exact quotient counts whole iterations, without byte slack. -/
theorem constant_stride_cost (code) (counter marker : MlS) (body : ProgHOL 64) (price stride length : Nat)
    (positive : 0<stride) (small : length<2^63) (aligned : stride∣length)
    (priced : ClockCost.Bound code body price) (advance : Advances counter stride body) (safe : LocalPrefix marker body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code=code) (cell : source.locals.lookup counter=some (.val (.word word)))
    (initial : word.toNat≤length) (wordAligned : stride∣word.toNat) :
    source.clock-(evaluateHOLFiniteState source (.while (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length))) body)).2.clock≤
      (price+1)*((length-word.toNat)/stride) := by
  classical
  let invariant:=fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ current : BitVec 64,state.locals.lookup counter=some (.val (.word current)) ∧ current.toNat≤length ∧ stride∣current.toNat
  let rank:=fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    (length-(counterWord state counter).toNat)/stride
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,state.code=code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=some (.val (.word observed)) → observed≠0 →
      0<rank state ∧ (state.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite state) body
        (output.1=none ∨ output.1=some .continue) → invariant output.2 ∧ rank output.2<rank state) := by
    intro state codeEq ready observed actual nonzero
    obtain ⟨current,currentCell,bounded,currentAligned⟩:=ready
    have number : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have currentSmall : current.toNat<9223372036854775808:=by omega
    have lengthSmall : length<9223372036854775808:=small
    have read : evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=
        some (.val (.word (if current.toNat<length then 1#64 else 0#64))) := by
      simp [evalHOLFinite,evalHOLExact,toExact,currentCell,wordCmpHOL,holAsmSignedLess,number,currentSmall,lengthSmall]
    have active : current.toNat<length := by
      by_contra inactive
      rw [if_neg inactive] at read
      have zero : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero zero
    have step : stride≤length-current.toNat:=Nat.le_of_dvd (by omega) (Nat.dvd_sub aligned currentAligned)
    have rankEq : rank state=(length-current.toNat)/stride:=by simp [rank,counterWord,currentCell,valueWord]
    refine ⟨by rw [rankEq]; exact Nat.div_pos step positive,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary:=safe.summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1=none:=continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body=(none,output.2):=Prod.ext normal rfl
    have nextCell:=advance (decClockHOLFinite state) output.2 current currentCell run
    have strideSmall : stride<2^64:=by omega
    have nextNumber : (current+BitVec.ofNat 64 stride).toNat=current.toNat+stride := by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]
    have nextRank : rank output.2=(length-(current.toNat+stride))/stride:=by
      simp only [rank,counterWord,nextCell,Option.getD_some,valueWord,nextNumber]
    have difference : length-current.toNat=(length-(current.toNat+stride))+stride:=by omega
    refine ⟨⟨current+BitVec.ofNat 64 stride,nextCell,by rw [nextNumber]; omega,by rw [nextNumber]; exact Nat.dvd_add currentAligned (dvd_refl stride)⟩,?_⟩
    rw [nextRank,rankEq,difference,Nat.add_div_right _ positive]
    omega
  have cost:=ClockCost.ranked_loop code _ body price invariant rank priced progress source installed ⟨word,cell,initial,wordAligned⟩
  simpa only [rank,counterWord,cell,Option.getD_some,valueWord] using cost

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.constant_stride_cost
