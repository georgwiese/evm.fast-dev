import InitECandidate.Solver.Input.CurrentRlp.Code
import InitECandidate.Solver.Input.RlpWrite.PutBeBuilt
import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.ByteStoreClock
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.CurrentRlp.PutBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open RlpWrite.PutBe hiding body

abbrev body := Code.body .putBe

theorem current_body : body=RlpWrite.PutBe.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_put_be")=some (RlpWrite.PutBe.formals,body,.one) := by
    have known:=Code.installed code installed .putBe
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_put_be,paramToHOL,shapeToHOL,List.map_cons,List.map_nil,RlpWrite.PutBe.formals] using known

theorem body_summary (key : MlS) (notIndex : key≠ofString "i") (notValue : key≠ofString "v") :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key loopBody source := by
  unfold loopBody
  exact local_summary_sequence key _ _ (LocalPrefix.assign _ _ notIndex).summary_full
    (local_summary_sequence key _ _ (byte_store_local key _ _) (LocalPrefix.assign _ _ notValue).summary_full)

theorem step_cost (code) : ClockCost.Bound code loopBody 0 :=
  ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _)
    (ClockCost.sequence code _ _ 0 0 (ClockCost.store_byte code _ _) (ClockCost.assign code _ _))

def Valid (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∃ index : BitVec 64,source.locals.lookup (ofString "i")=some (.val (.word index))
def rank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  (CounterFlow.counterWord source (ofString "i")).toNat

/-- Only a genuinely continuing body must carry the decreased counter.
A missing value or failed byte store stops without a later-state premise. -/
theorem step_progress (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Valid source)
    (observed : BitVec 64) (read : eval source test=some (.val (.word observed))) (nonzero : observed≠0#64) :
    0<rank source ∧ (source.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite source) loopBody;
      (output.1=none ∨ output.1=some .continue)→Valid output.2 ∧ rank output.2<rank source) := by
  obtain ⟨index,indexCell⟩:=valid
  have expected : eval source test=some (.val (.word (if 0<index.toNat then 1#64 else 0#64))):=by
    simp [eval,test,evalHOLExact,toExact,localVar,indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  have positive : 0<index.toNat:=by
    by_cases positive : 0<index.toNat
    · exact positive
    · rw [if_neg positive] at expected
      have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact (nonzero zero).elim
  have rankEq : rank source=index.toNat:=by simp [rank,CounterFlow.counterWord,indexCell,valueWord]
  refine ⟨by rw [rankEq]; exact positive,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output:=evaluateHOLFiniteState (decClockHOLFinite source) loopBody
  have summary:=body_summary (ofString "n") (by decide) (by decide) (decClockHOLFinite source)
  unfold LocalSummary at summary
  have normal : output.1=none:=continuing.resolve_right summary.2.2.2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) loopBody=(none,output.2):=Prod.ext normal rfl
  obtain ⟨middle,assigned,tailRun⟩:=sequence_none (decClockHOLFinite source) output.2 _ _ run
  have subRead : eval (decClockHOLFinite source) decrement=some (.val (.word (index-1#64))):=by
    simp [eval,decrement,decClockHOLExact,evalHOLExact,evalListHOLExact,toExact,localVar,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have middleEq:=assign_none (decClockHOLFinite source) middle "i" decrement (index-1#64) subRead assigned
  have kept:=local_summary_sequence (ofString "i") (.storeByte address (localVar "v")) (.assign .local (ofString "v") shifted)
    (byte_store_local (ofString "i") _ _) (LocalPrefix.assign _ _ (by decide)).summary_full middle
  unfold LocalSummary at kept
  rw [tailRun] at kept
  have nextIndex : output.2.locals.lookup (ofString "i")=some (.val (.word (index-1#64))):=by
    rw [kept.1 rfl,middleEq]
    exact bind_lookup_same _ _ _
  have number : (index-1#64).toNat=index.toNat-1:=by
    rw [BitVec.toNat_sub_of_le (by change 1≤index.toNat; omega)]
    rfl
  have nextRank : rank output.2=(index-1#64).toNat:=by simp [rank,CounterFlow.counterWord,nextIndex,valueWord]
  refine ⟨⟨index-1#64,nextIndex⟩,?_⟩
  change rank output.2<rank source
  rw [nextRank,number,rankEq]
  omega

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤index.toNat := by
  have price:=ClockCost.ranked_loop source.code test loopBody 0 Valid rank (step_cost source.code)
    (by intro current codeEq ready word read nonzero; exact step_progress current ready word read nonzero) source rfl ⟨index,indexCell⟩
  simpa only [Nat.zero_add,Nat.one_mul,loop,rank,CounterFlow.counterWord,indexCell,Option.getD_some,valueWord] using price

/-- Actual current reverse byte writing takes at most its input count on
every outcome, including clock exhaustion and unmapped output. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤count.toNat := by
  rw [current_body,body_shape]
  have read : eval source (localVar "n")=some (.val (.word count)):=by simpa only [eval,evalHOLExact,toExact,localVar] using countCell
  apply ClockCost.declared_current source "i" (localVar "n") count tail _ read
  let entered:=bind source "i" count
  exact ClockCost.sequence_current entered loop (.return (.const 0#64)) count.toNat 0
    (loop_cost entered count (bind_lookup_same _ _ _)) (ClockCost.returned source.code _)


/-- Actual ignored callers pay at most one tick plus their scalar count,
using the fixed software entry and the caller's observed arguments. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst word count : BitVec 64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word word),.val (.word count)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_put_be") arguments)).2.clock≤count.toNat+1 := by
  have code:=original_code source.code installed
  obtain ⟨callee,called,dCell,vCell,nCell⟩:=environment source.code.lookup dst word count code
  exact ClockCost.call_current source (some none) (ofString "rlp_put_be") arguments _ body callee .one count.toNat args called
    (body_cost (callEntryStateHOLFinite source callee) count nCell)

end InitECandidate.Solver.Input.CurrentRlp.PutBe

#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.body_summary
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.step_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.step_progress
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.body_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.call_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.original_code
