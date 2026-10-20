import InitECandidate.Solver.Input.ProgressiveStepCost
import InitECandidate.Solver.Input.ProgressiveStepNormal
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def valid (p roots cursor zeros stp accel : BitVec 64) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ k : Nat,k≤15 ∧ RoundState source p roots cursor zeros stp accel n k

def remaining (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  allowance n (CounterFlow.counterWord source (ofString "off")).toNat (CounterFlow.counterWord source (ofString "k")).toNat

theorem word_geometry (k : Nat) (inside : k≤15) :
    (BitVec.ofNat 64 (offset k)).toNat=offset k ∧ (BitVec.ofNat 64 (4^k)).toNat=4^k ∧ (BitVec.ofNat 64 k).toNat=k := by
  have offBound := offset_mono inside
  have exactOffset : offset 15=357913941 := by decide
  rw [exactOffset] at offBound
  have sizeBound : 4^k≤4^15 := Nat.pow_le_pow_right (by decide) inside
  have ceiling : 4^15=1073741824 := by decide
  rw [ceiling] at sizeBound
  exact ⟨by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)],by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)],by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]⟩

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=
      some (.val (.word (if offset k<n then 1#64 else 0#64))) := by
  have offNumber := (word_geometry k inside).1
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,test,localVar,actual.position,actual.count,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,offNumber,nNumber]

private theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word))) (nonzero : word≠0) : offset k<n := by
  have expected := test_read source p roots cursor zeros stp accel n k bounded inside actual
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) : remaining n source=allowance n (offset k) k := by
  have numbers := word_geometry k inside
  simp only [remaining,CounterFlow.counterWord,actual.position,actual.round,Option.getD_some,valueWord,numbers.1,numbers.2.2]

/-- Original progressive Merkle rounds amortize over actual capped input
chunks. The limit is a logarithmic round cost; no full-capacity charge is
multiplied by a separate number of rounds. All non-timeout failures remain. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) (mapped : Geometry p roots cursor zeros n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source loop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤allowance n (offset k) k := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots cursor zeros stp accel n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) step
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid p roots cursor zeros stp accel n output.2 ∧
          current.clock-output.2.clock+remaining n output.2≤remaining n current) := by
    intro current codeEq currentValid word read nonzero funded
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current p roots cursor zeros stp accel n position bounded positionBound ready word read nonzero
    have round := active_round n position bounded active
    have geometric := round_geometry n position bounded active
    have entryReady := RoundState.dec_clock current p roots cursor zeros stp accel n position ready
    let output := evaluateHOLFiniteState (decClockHOLFinite current) step
    dsimp only
    intro bodyNotTimeout
    have bodyCost : current.clock-1-output.2.clock≤115*min (4^position) (n-offset position)+55*(2*position)+14 :=
      step_cost (decClockHOLFinite current) output.2 p roots cursor zeros stp accel n position bounded active entryReady mapped output.1 rfl bodyNotTimeout
    have bodyClock : output.2.clock≤current.clock-1 := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) step
    have currentAllowance := remaining_read current p roots cursor zeros stp accel n position positionBound ready
    have amortized := amortized_round n (offset position) (4^position) position active (Nat.pow_pos (by decide)) round
    have overhead := round_price position round
    have stopped : current.clock-output.2.clock≤remaining n current := by
      rw [currentAllowance]
      omega
    refine ⟨stopped,?_⟩
    intro continuing
    have summary := (step_other (ofString "p") (by decide) (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) step=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 p roots cursor zeros stp accel n position bounded active entryReady mapped bodyRun
    have nextBound : position+1≤15 := by omega
    have nextAllowance := remaining_read output.2 p roots cursor zeros stp accel n (position+1) nextBound next
    have paid : current.clock-output.2.clock+remaining n output.2≤remaining n current := by
      rw [currentAllowance,nextAllowance]
      change current.clock-output.2.clock+allowance n (offset position+4^position) (position+1)≤allowance n (offset position) position
      omega
    exact ⟨⟨position+1,nextBound,next⟩,paid⟩
  have observed : (evaluateHOLFiniteState source (.while test step)).1≠some .timeOut := by
    rw [←loop_shape.1,run]
    exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code test step (valid p roots cursor zeros stp accel n) (remaining n) priced source rfl ⟨k,inside,actual⟩ observed
  rw [←loop_shape.1,run] at price
  change source.clock-post.clock≤remaining n source at price
  rw [remaining_read source p roots cursor zeros stp accel n k inside actual] at price
  exact price

/-- The same real normal loop exit retains its checked round state, original
heap cursor, SHA environment and an in-range root count. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) (mapped : Geometry p roots cursor zeros n)
    (run : evaluateHOLFiniteState source loop=(none,post)) : valid p roots cursor zeros stp accel n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots cursor zeros stp accel n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) step=(none,target) → valid p roots cursor zeros stp accel n target := by
    intro current codeEq currentValid word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current p roots cursor zeros stp accel n position bounded positionBound ready word read nonzero
    have next := step_normal (decClockHOLFinite current) target p roots cursor zeros stp accel n position bounded active
      (RoundState.dec_clock current p roots cursor zeros stp accel n position ready) mapped bodyRun
    exact ⟨position+1,by have limit:=active_round n position bounded active; omega,next⟩
  rw [loop_shape.1] at run
  exact loop_invariant source.code (ofString "p") test step (step_other (ofString "p") (by decide) (by decide) (by decide) (by decide))
    (valid p roots cursor zeros stp accel n) transition source post rfl ⟨k,inside,actual⟩ run

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.word_geometry
#print axioms InitECandidate.Solver.Input.Progressive.test_read
#print axioms InitECandidate.Solver.Input.Progressive.remaining_read
#print axioms InitECandidate.Solver.Input.Progressive.loop_cost
#print axioms InitECandidate.Solver.Input.Progressive.loop_normal
