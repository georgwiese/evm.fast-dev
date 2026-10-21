import InitECandidate.Solver.Input.PayloadHashScopes
import InitECandidate.Solver.Input.HashFieldMemory
import InitECandidate.Solver.Input.CallArgumentsEqual
import InitECandidate.Solver.Input.HashInputRegion

namespace InitECandidate.Solver.Input.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev Field := FixedHash.Step

def inputExpression (field : Field) : ExpHOL 64 := .op .add [localVar "raw",.const (BitVec.ofNat 64 field.inputOffset)]
def outputExpression (slot : Nat) : ExpHOL 64 := FixedHash.offsetExpression "ch" (32*slot)
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
  simp only [afterChunks,afterMark,afterRaw,transactionScope,dropSequence,body,Guest.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,firstFields,middleFields,List.foldr_cons,List.foldr_nil,step,arguments,inputExpression,outputExpression,extraArguments,fieldExpression,
    FixedHash.Step.function,FixedHash.Step.inputOffset,FixedHash.Step.field,FixedHash.offsetExpression,localVar]
  rfl

set_option maxRecDepth 100000 in
/-- Actual last scalar/balance/container sequence after both real releases. -/
theorem final_shape : finalFields=program [.scalar 512 15,.scalar 520 16]
    (.seq (.call (some (none,none)) (ofString "htr_pbytes") balanceArguments)
      (.seq (step (.scalar 532 18)) (.seq (.call (some (none,none)) (ofString "htr_pcontainer") containerArguments) FixedHash.releaseSuffix))) := by
  simp only [finalFields,afterWithdrawalList,afterWithdrawalLoop,withdrawalLoopAndSuffix,afterWithdrawalAllocation,afterNwd,afterWd,withdrawalScope,
    afterTransactionList,afterTransactionLoop,transactionLoopAndSuffix,afterTxRoots,afterSecondMark,afterNtx,afterTxs,transactionScope,dropSequence,afterChunks,afterMark,afterRaw,
    body,Guest.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,List.foldr_cons,List.foldr_nil,step,arguments,inputExpression,outputExpression,balanceArguments,containerArguments,fieldExpression,FixedHash.releaseSuffix,
    FixedHash.Step.function,FixedHash.Step.inputOffset,FixedHash.Step.field,FixedHash.offsetExpression,localVar]
  rfl

theorem fields_fit : ∀ field∈firstFields++middleFields++lastFields,field.Fits 540 19 1600 := by
  simp [firstFields,middleFields,lastFields,FixedHash.Step.Fits,FixedHash.Step.inputOffset,FixedHash.Step.length,FixedHash.Step.field,PackBytes.chunks]

theorem field_prices : (firstFields.map FixedHash.Step.price).sum=1260 ∧ (middleFields.map FixedHash.Step.price).sum=10 ∧ (lastFields.map FixedHash.Step.price).sum=15 := by decide

theorem step_local (field : Field) (key : MlS) : LocalPrefix key (step field) := .call none _ _ (by intro name impossible; cases impossible)

theorem step_globals (field : Field) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code (step field) := by
  cases field with
  | scalar offset slot=>exact GlobalEffects.call_body key code (some none) (ofString "htr_u64_at") _ U64Hash.formals U64Hash.body .one (U64Hash.original_code code installed) (U64Hash.globals key code installed)
  | copy offset slot=>exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code)
  | vector offset length slot depth=>exact GlobalEffects.call_body key code (some none) (ofString "htr_bytes_vector") _ BytesVector.formals BytesVector.body .one (BytesVector.original_code code installed) (BytesVector.globals key code installed different)

end InitECandidate.Solver.Input.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.prefix_shape
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.final_shape
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.fields_fit
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.field_prices
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.step_local
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.step_globals
