import InitECandidate.Solver.Input.CurrentHash.PayloadScopes
import InitECandidate.Solver.Input.CurrentHash.FixedRecordSteps
import InitECandidate.Solver.Input.CallArgumentsEqual

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev Field := FixedRecord.Step

def inputExpression (field : Field) : ExpHOL 64 := .op .add [localVar "raw",.const (BitVec.ofNat 64 field.inputOffset)]
def outputExpression (slot : Nat) : ExpHOL 64 := FixedRecord.offsetExpression "ch" (32*slot)
def arguments (field : Field) : List (ExpHOL 64) :=
  match field with
  | .scalar _ slot=>[inputExpression field,outputExpression slot]
  | .copy _ slot=>[outputExpression slot,inputExpression field,.const 32#64]
  | .vector _ length slot _=>[inputExpression field,.const (BitVec.ofNat 64 length),outputExpression slot]
def step (field : Field) : ProgHOL 64 := .call (some (none,none)) field.function (arguments field)
def program (fields : List Field) (tail : ProgHOL 64) : ProgHOL 64 := fields.foldr (fun field rest=>.seq (step field) rest) tail

def firstFields : List Field := [.copy 0 0,.vector 32 20 1 0,.copy 52 2,.copy 84 3,.vector 116 256 4 3,.copy 372 5,
  .scalar 404 6,.scalar 412 7,.scalar 420 8,.scalar 428 9]
def middleFields : List Field := [.copy 440 11,.copy 472 12]
def lastFields : List Field := [.scalar 512 15,.scalar 520 16,.scalar 532 18]
def extraArguments : List (ExpHOL 64) := [fieldExpression 16,fieldExpression 24,.const 1#64,outputExpression 10]
def balanceArguments : List (ExpHOL 64) := [fieldExpression 64,fieldExpression 72,outputExpression 17]
def containerArguments : List (ExpHOL 64) := [localVar "ch",.const 19#64,localVar "out"]

set_option maxRecDepth 100000 in
/-- Literal original payload prefix, including raw+0 and actual extra-data
loads. This is a kernel-matched proof template, not a different hasher. -/
theorem prefix_shape : afterChunks=program firstFields (.seq (.call (some (none,none)) (ofString "htr_bytes_list") extraArguments) (program middleFields transactionScope)) := by
  simp only [afterChunks,afterMark,afterRaw,transactionScope,dropSequence,body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,firstFields,middleFields,List.foldr_cons,List.foldr_nil,step,arguments,inputExpression,outputExpression,extraArguments,fieldExpression,
    FixedRecord.Step.function,FixedRecord.Step.inputOffset,FixedRecord.Step.field,FixedRecord.offsetExpression,localVar]
  rfl

set_option maxRecDepth 100000 in
/-- Actual last scalar/balance/container sequence after both real releases. -/
theorem final_shape : finalFields=program [.scalar 512 15,.scalar 520 16]
    (.seq (.call (some (none,none)) (ofString "htr_pbytes") balanceArguments)
      (.seq (step (.scalar 532 18)) (.seq (.call (some (none,none)) (ofString "htr_pcontainer") containerArguments) FixedRecord.releaseSuffix))) := by
  simp only [finalFields,afterWithdrawalList,afterWithdrawalLoop,withdrawalLoopAndSuffix,afterWithdrawalAllocation,afterNwd,afterWd,withdrawalScope,
    afterTransactionList,afterTransactionLoop,transactionLoopAndSuffix,afterTxRoots,afterSecondMark,afterNtx,afterTxs,transactionScope,dropSequence,afterChunks,afterMark,afterRaw,
    body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,List.foldr_cons,List.foldr_nil,step,arguments,inputExpression,outputExpression,balanceArguments,containerArguments,fieldExpression,FixedRecord.releaseSuffix,
    FixedRecord.Step.function,FixedRecord.Step.inputOffset,FixedRecord.Step.field,FixedRecord.offsetExpression,localVar]
  rfl

theorem fields_valid : ∀ field∈firstFields++middleFields++lastFields,
    field.Valid ∧ field.inputOffset+field.length≤540 ∧ field.field<19 := by
  simp [firstFields,middleFields,lastFields,FixedRecord.Step.Valid,FixedRecord.Step.inputOffset,FixedRecord.Step.length,FixedRecord.Step.field,PackBytes.chunks]

theorem field_prices : (firstFields.map FixedRecord.Step.price).sum=1668 ∧ (middleFields.map FixedRecord.Step.price).sum=84 ∧ (lastFields.map FixedRecord.Step.price).sum=162 := by decide

theorem step_local (field : Field) (key : MlS) : LocalPrefix key (step field) := .call none _ _ (by intro name impossible; cases impossible)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.final_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.fields_valid
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.field_prices
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.step_local
