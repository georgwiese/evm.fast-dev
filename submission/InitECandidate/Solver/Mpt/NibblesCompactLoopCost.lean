import InitECandidate.Solver.Mpt.NibblesCompactProgram
import InitECandidate.Solver.Input.CounterStrideLoop

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual counter and parity of the remaining physical path. The path
may exceed the maximum query-key length. No successful byte read is assumed. -/
def LoopValid (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∃ index : BitVec 64,source.locals.lookup (ofString "i")=some (.val (.word index)) ∧
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧
    index.toNat≤length ∧ (length-index.toNat)%2=0

def loopRank (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  (length-(Input.CounterFlow.counterWord source (ofString "i")).toNat)/2

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (index : BitVec 64)
    (small : length<2^64)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source test=some (.val (.word (if index.toNat<length then 1#64 else 0#64))) := by
  have reduced : length%18446744073709551616=length:=Nat.mod_eq_of_lt small
  simp [eval,test,evalHOLExact,toExact,localVar,indexCell,lengthCell,reduced,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

theorem loop_transition (length : Nat) (small : length<2^64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : LoopValid length source)
    (observed : BitVec 64) (read : eval source test=some (.val (.word observed))) (nonzero : observed≠0#64) :
    0<loopRank length source ∧ (source.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite source) step;
      (output.1=none ∨ output.1=some .continue)→LoopValid length output.2 ∧ loopRank length output.2<loopRank length source) := by
  obtain ⟨index,indexCell,lengthCell,inside,parity⟩:=valid
  have expected:=test_read source length index small indexCell lengthCell
  have active : index.toNat<length:=by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have enough : index.toNat+2≤length:=by omega
  have rankEq : loopRank length source=(length-index.toNat)/2:=by simp [loopRank,Input.CounterFlow.counterWord,indexCell,valueWord]
  refine ⟨by rw [rankEq]; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output:=evaluateHOLFiniteState (decClockHOLFinite source) step
  have summary:=step_summary (ofString "n") (by decide) (by decide) (decClockHOLFinite source)
  unfold Input.LocalSummary at summary
  have normal : output.1=none:=continuing.resolve_right summary.2.2.2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) step=(none,output.2):=Prod.ext normal rfl
  have nextIndex:=step_advance (decClockHOLFinite source) output.2 index indexCell run
  have nextLength:=(summary.1 normal).trans lengthCell
  have number : (index+2#64).toNat=index.toNat+2:=by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+2<2^64; omega)]
    rfl
  have nextRank : loopRank length output.2=(length-(index.toNat+2))/2:=by simp [loopRank,Input.CounterFlow.counterWord,nextIndex,valueWord,number]
  exact ⟨⟨index+2#64,nextIndex,nextLength,(by rw [number]; omega),(by rw [number]; omega)⟩,by rw [rankEq,nextRank]; omega⟩

/-- Every actual loop outcome spends at most one source tick per pair of
remaining nibbles. Real byte errors stop without requiring a future model. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^64) (valid : LoopValid length source) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤loopRank length source := by
  rw [body_shapes.2.2.2.2.2.1]
  simpa only [Nat.zero_add,Nat.one_mul] using
    Input.ClockCost.ranked_loop source.code test step 0 (LoopValid length) (loopRank length) (step_cost source.code)
      (by intro current codeEq ready word read nonzero; exact loop_transition length small current ready word read nonzero)
      source rfl valid

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.test_read
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.loop_transition
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.loop_cost
