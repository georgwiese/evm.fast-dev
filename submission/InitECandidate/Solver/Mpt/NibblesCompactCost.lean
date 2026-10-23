import InitECandidate.Solver.Mpt.NibblesCompactLoopCost
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.LocalSummaryConditional
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem header_summary (key : MlS) (different : key≠ofString "i") :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary key header source := by
  rw [body_shapes.2.2.2.2.2.2.2]
  exact Input.local_summary_conditional key _ _ _ (Input.byte_store_local key _ _)
    (Input.local_summary_sequence key _ _ (Input.byte_store_local key _ _) (Input.LocalPrefix.assign _ _ different).summary_full)

/-- The actual header chooses the counter parity; a failed byte store
does not provide continuation. No nibble/pointer readability is required. -/
theorem header_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source header=(none,target)) :
    target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (length.toNat%2)))) ∧
      target.locals.lookup (ofString "n")=some (.val (.word length)) := by
  have kept:=header_summary (ofString "n") (by decide) source
  unfold Input.LocalSummary at kept
  rw [normal] at kept
  have equal : (length&&&1#64=0#64)↔length.toNat%2=0:=by
    constructor
    · intro same
      have number:=congrArg BitVec.toNat same
      simpa [BitVec.toNat_and,Nat.and_one_is_mod] using number
    · intro same
      apply BitVec.eq_of_toNat_eq
      simpa [BitVec.toNat_and,Nat.and_one_is_mod] using same
  have selected : evaluateHOLFiniteState source header=
      if length.toNat%2=0 then evaluateHOLFiniteState source evenHeader else
        evaluateHOLFiniteState source (.seq oddStore (.assign .local (ofString "i") (.const 1#64))):=by
    rw [body_shapes.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite]
    simp [evenTest,evalHOLExact,evalListHOLExact,toExact,localVar,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    change (if length&&&1#64=0#64 then evaluateHOLFiniteState source evenHeader else
      evaluateHOLFiniteState source (.seq oddStore (.assign .local (ofString "i") (.const 1#64))))=_
    simp only [equal]
  refine ⟨?_,(kept.1 rfl).trans lengthCell⟩
  by_cases even : length.toNat%2=0
  · rw [if_pos even] at selected
    have summary:=Input.byte_store_local (ofString "i") (localVar "dst") (.panop .mul [.const 16#64,localVar "flag"]) source
    change Input.LocalSummary (ofString "i") evenHeader source at summary
    unfold Input.LocalSummary at summary
    rw [←selected,normal] at summary
    simpa only [even] using (summary.1 rfl).trans indexCell
  · rw [if_neg even] at selected
    obtain ⟨middle,stored,assigned⟩:=Input.sequence_none source target oddStore _ (selected.symm.trans normal)
    have postEq:=Input.assign_none middle target "i" (.const 1#64) 1#64 rfl assigned
    have odd : length.toNat%2=1:=by omega
    rw [postEq,odd]
    exact bind_lookup_same _ _ _

theorem after_output_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^64) (valid : LoopValid length source) :
    source.clock-(evaluateHOLFiniteState source afterOutput).2.clock≤loopRank length source := by
  rw [body_shapes.2.2.2.2.1]
  exact Input.ClockCost.sequence_current source loop (.return (localVar "o")) (loopRank length source) 0
    (loop_cost source length small valid) (Input.ClockCost.returned source.code _)

/-- Whole original compact writer: at most floor(n/2) source ticks on
every outcome, with no artificial64-nibble cap on stored paths. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length leaf : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (leafCell : source.locals.lookup (ofString "is_leaf")=some (.val (.word leaf))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length.toNat/2 := by
  have flagRead : eval source flagExpression=some (.val (.word (leaf*2#64))):=by
    simp [eval,flagExpression,evalHOLExact,evalListHOLExact,toExact,localVar,leafCell,valueIsWord,valueWord,panOpHOL]
  let flagged:=bind source "flag" (leaf*2#64)
  let entered:=bind flagged "i" 0#64
  have currentLength : entered.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other flagged "i" "n" 0#64 (by decide)).trans
      ((bind_lookup_other source "flag" "n" (leaf*2#64) (by decide)).trans lengthCell)
  have suffix (current : PanSemStateFiniteExact 64 Guest.HostMemory) (run : evaluateHOLFiniteState entered header=(none,current)) :
      current.clock-(evaluateHOLFiniteState current outputScope).2.clock≤length.toNat/2:=by
    obtain ⟨index,nextLength⟩:=header_normal entered current length currentLength (bind_lookup_same _ _ _) run
    let outputReady:=bind current "o" 1#64
    have actualIndex : outputReady.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (length.toNat%2)))):=
      (bind_lookup_other current "o" "i" 1#64 (by decide)).trans index
    have actualLength : outputReady.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))):=by
      simpa using (bind_lookup_other current "o" "n" 1#64 (by decide)).trans nextLength
    have valid : LoopValid length.toNat outputReady:=by
      refine ⟨BitVec.ofNat 64 (length.toNat%2),actualIndex,actualLength,?_,?_⟩
      all_goals
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show length.toNat%2<2^64 by omega)]
        omega
    have price:=after_output_cost outputReady length.toNat length.isLt valid
    have rankEq : loopRank length.toNat outputReady=length.toNat/2:=by
      simp only [loopRank,Input.CounterFlow.counterWord,actualIndex,Option.getD_some,valueWord,BitVec.toNat_ofNat]
      have modulus : (length.toNat%2)%2^64=length.toNat%2:=Nat.mod_eq_of_lt (by omega)
      rw [modulus]
      omega
    rw [body_shapes.2.2.2.1]
    apply Input.ClockCost.declared_current current "o" (.const 1#64) 1#64 afterOutput (length.toNat/2) rfl
    simpa only [rankEq] using price
  have priced:=Input.ClockCost.sequence_reached_current entered header outputScope 0 (length.toNat/2) (header_cost entered.code entered rfl) suffix
  rw [body_shapes.1]
  apply Input.ClockCost.declared_current source "flag" flagExpression (leaf*2#64) afterFlag _ flagRead
  rw [body_shapes.2.1]
  apply Input.ClockCost.declared_current flagged "i" (.const 0#64) 0#64 afterCounter _ rfl
  rw [body_shapes.2.2.1]
  simpa only [Nat.zero_add] using priced

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.header_summary
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.header_normal
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.after_output_cost
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.body_cost
