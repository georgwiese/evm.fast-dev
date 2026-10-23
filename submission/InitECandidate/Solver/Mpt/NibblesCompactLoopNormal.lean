import InitECandidate.Solver.Mpt.NibblesCompactCost
import InitECandidate.Solver.Input.LoopSummaryInvariant
import InitECandidate.Solver.Input.LoopNormalExit

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def OutputValid (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  LoopValid length source ∧ ∃ output : BitVec 64,source.locals.lookup (ofString "o")=some (.val (.word output)) ∧
    output.toNat=(Input.CounterFlow.counterWord source (ofString "i")).toNat/2+1

theorem step_output_advance : Input.CounterFlow.Advances (ofString "o") 1 step := by
  rw [body_shapes.2.2.2.2.2.2.1,store_pair_shape]
  simpa only [Nat.zero_add,advance,advanceOutput,localVar] using
    Input.CounterFlow.sequence (ofString "o") _ _ 0 (0+1) (Input.CounterFlow.byte_store _ _ _)
      (Input.CounterFlow.sequence (ofString "o") _ _ 0 1
        (Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))) (Input.CounterFlow.increment _))

/-- Both real counter assignments retain the output/index relation. The
parity of the actual active path prevents either assignment from wrapping. -/
theorem output_transition (length : Nat) (small : length<2^64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : OutputValid length source)
    (observed : BitVec 64) (read : eval source test=some (.val (.word observed))) (nonzero : observed≠0#64)
    (funded : source.clock≠0) (run : evaluateHOLFiniteState (decClockHOLFinite source) step=(none,target)) :
    OutputValid length target := by
  have nextValid:=(loop_transition length small source valid.1 observed read nonzero).2 funded
  rw [run] at nextValid
  have next:=(nextValid (Or.inl rfl)).1
  obtain ⟨index,indexCell,lengthCell,inside,parity⟩:=valid.1
  obtain ⟨output,outputCell,relation⟩:=valid.2
  have currentNumber : (Input.CounterFlow.counterWord source (ofString "i")).toNat=index.toNat:=by
    simp [Input.CounterFlow.counterWord,indexCell,valueWord]
  rw [currentNumber] at relation
  have expected:=test_read source length index small indexCell lengthCell
  have active : index.toNat<length:=by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have enough : index.toNat+2≤length:=by omega
  have indexNumber : (index+2#64).toNat=index.toNat+2:=by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+2<2^64; omega)]
    rfl
  have outputNumber : (output+1#64).toNat=output.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change output.toNat+1<2^64; omega)]
    rfl
  have nextIndex:=step_advance (decClockHOLFinite source) target index indexCell run
  have nextOutput:=step_output_advance (decClockHOLFinite source) target output outputCell run
  refine ⟨next,output+1#64,nextOutput,?_⟩
  simp only [Input.CounterFlow.counterWord,nextIndex,Option.getD_some,valueWord,indexNumber,outputNumber]
  omega

/-- A genuine normal compact loop ends at the real path length, with
exactly floor(n/2)+1 output bytes. No completed trace is supplied as a model. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^64) (valid : OutputValid length source)
    (run : evaluateHOLFiniteState source loop=(none,target)) :
    target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      ∃ output : BitVec 64,target.locals.lookup (ofString "o")=some (.val (.word output)) ∧ output.toNat=length/2+1 := by
  have shaped:=run
  rw [body_shapes.2.2.2.2.2.1] at shaped
  have finalValid:=Input.loop_invariant_summary source.code (ofString "n") test step
    (step_summary (ofString "n") (by decide) (by decide)) (OutputValid length)
    (by intro current codeEq ready word read nonzero funded post bodyRun; exact output_transition length small current post ready word read nonzero funded bodyRun)
    source target rfl valid shaped
  have exit:=Input.loop_normal_exit test step (fun current=>(step_summary (ofString "n") (by decide) (by decide) current).2.2.1) source target shaped
  change eval target test=some (.val (.word 0#64)) at exit
  obtain ⟨⟨index,indexCell,lengthCell,inside,parity⟩,output,outputCell,relation⟩:=finalValid
  have expected:=test_read target length index small indexCell lengthCell
  have endpoint : index.toNat=length:=by
    by_contra unequal
    have active : index.toNat<length:=by omega
    rw [if_pos active,exit] at expected
    cases expected
  have wordEq : index=BitVec.ofNat 64 length:=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,endpoint]
  refine ⟨by rw [←wordEq]; exact indexCell,output,outputCell,?_⟩
  simpa only [Input.CounterFlow.counterWord,indexCell,Option.getD_some,valueWord,endpoint] using relation

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.step_output_advance
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.output_transition
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.loop_normal
