import InitECandidate.Solver.GasBudget.ForwardBudget

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def debitExpression : ExpHOL 64 := .rfield 0 (localVar "mcg")
def forwardedExpression : ExpHOL 64 := .rfield 1 (localVar "mcg")
def counterExpression : ExpHOL 64 := .op .sub [frameLoad 184#64,forwardedExpression]
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "charge_gas") [debitExpression])
    (.seq (.store (frameAddress 184#64) counterExpression) continuation)

/-- Actual charge of the debit and subtraction of the forwarded amount from
the used counter. The child seed is accounted for in the resulting equality. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left used requested : BitVec 64) (words : U256Zero.Quad)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mcg : source.locals.lookup (ofString "mcg")=some (CallGas.pair (CallGas.capped requested left) (CallGas.capped requested left+CallGas.stipend words)))
    (gasMapped : source.memaddrs (frame+64#64)) (usedMapped : source.memaddrs (frame+184#64))
    (gasCell : source.memory (frame+64#64)=.word left) (usedCell : source.memory (frame+184#64)=.word used)
    (code : source.code.lookup (ofString "charge_gas")=some (RegularCharge.formals,RegularCharge.body,.one))
    (leftFits : left.toNat+2300<2^64) (budgetFits : left.toNat+used.toNat<2^64)
    (funded : (CallGas.stipend words).toNat≤used.toNat) (enough : 1≤source.clock) :
    ∃ target,target={source with memory:=target.memory,clock:=source.clock-1} ∧
      regularBudget target.memory frame+(CallGas.capped requested left+CallGas.stipend words).toNat=regularBudget source.memory frame ∧
      (∀ continuation,evaluateHOLFiniteState source (program continuation)=evaluateHOLFiniteState target continuation) := by
  classical
  let debit:=CallGas.capped requested left
  let forwarded:=debit+CallGas.stipend words
  have debitBound : debit≤left:=(CallGas.capped_number requested left).2
  have debitRead : eval source debitExpression=some (.val (.word debit)) := by
    simp [eval,debitExpression,evalHOLExact,toExact,localVar,mcg,CallGas.pair,debit]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [debitExpression]=some [.val (.word debit)] := by
    simp only [eval] at debitRead
    simp only [evalListHOLFinite,evalListHOLExact,debitRead]
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" RegularCharge.body debit code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨post,run,memoryEq,frameEq⟩:=RegularCharge.execute entry frame left used debit ev amountLocal gasMapped usedMapped gasCell usedCell debitBound
  have callRun:=ignored_return source post _ [debitExpression] _ RegularCharge.body callee 1 args called enough run frameEq
  rw [memoryEq] at callRun
  let memory:=WitnessRadix.WordWrites.write source.memory (RegularCharge.writes frame left used debit)
  let charged:={source with memory:=memory,clock:=source.clock-1}
  have storedUsed : charged.memory (frame+184#64)=.word (used+debit) :=
    WitnessRadix.WordWrites.write_unique source.memory (RegularCharge.writes frame left used debit) (frame+184#64,used+debit)
      (by simp [RegularCharge.writes,offsets_ne frame 64#64 184#64 (by decide)]) (by simp [RegularCharge.writes])
  have mcgC : charged.locals.lookup (ofString "mcg")=some (CallGas.pair debit forwarded):=mcg
  have forwardedRead : eval charged forwardedExpression=some (.val (.word forwarded)) := by
    simp [eval,forwardedExpression,evalHOLExact,toExact,localVar,mcgC,CallGas.pair]
  have usedRead:=frame_read charged frame 184#64 (used+debit) ev usedMapped storedUsed
  have counterRead : eval charged counterExpression=some (.val (.word ((used+debit)-forwarded))) := by
    simp only [eval] at usedRead forwardedRead ⊢
    simp only [counterExpression,evalHOLExact,evalListHOLExact,usedRead,forwardedRead]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp]
  have counterRun:=WitnessRadix.StoreWord.execute charged (frameAddress 184#64) counterExpression (frame+184#64) ((used+debit)-forwarded)
    (address_read charged frame 184#64 ev) counterRead usedMapped
  let target:={charged with memory:=WitnessRadix.StoreWord.put memory (frame+184#64) ((used+debit)-forwarded)}
  have debitNative : debit.toNat≤left.toNat:=debitBound
  have forwardedNative : forwarded.toNat=debit.toNat+(CallGas.stipend words).toNat:=
    (CallGas.forwarded_number words requested left leftFits).2
  have usedNative : (used+debit).toNat=used.toNat+debit.toNat:=BitVec.toNat_add_of_lt (by omega)
  have forwardedAffordable : forwarded≤used+debit := by
    change forwarded.toNat≤(used+debit).toNat
    rw [forwardedNative,usedNative]
    omega
  have debitBudget:=used_debit_budget memory frame (used+debit) forwarded storedUsed forwardedAffordable
  have chargeBudget:=(RegularCharge.quantitative source frame left used debit gasCell usedCell debitBound budgetFits).1
  refine ⟨target,rfl,debitBudget.trans chargeBudget,?_⟩
  intro continuation
  rw [program,WitnessRadix.StateSteps.next_sequence source charged _ _ callRun (by change source.clock-1≤source.clock; omega),
    WitnessRadix.StateSteps.next_sequence charged target _ _ counterRun (Nat.le_refl _)]

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.execute
