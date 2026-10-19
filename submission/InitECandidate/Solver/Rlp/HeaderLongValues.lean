import InitECandidate.Solver.Rlp.HeaderShortValues
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

theorem after_read_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length ll payload flag : BitVec 64)
    (small : ll.toNat≤8) (room : 1+ll.toNat≤length.toNat) (binary : flag=0#64 ∨ flag=1#64)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterRead flag)=(some (.returned returned),post)) : Valid length.toNat returned := by
  obtain ⟨canonicalRun,afterCanonical⟩ := Fail.guard_return source post _ [.const 5#64] _ returned installed normal
  have leftRead : eval source (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"])=some (.val (.word (length-1#64-ll))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,lengthCell,llCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval source (localVar "n")=some (.val (.word payload)) := by simp [eval,evalHOLExact,localVar,toExact,payloadCell]
  obtain ⟨bound,tailRun⟩ := Fail.lower_guard_return source post _ _ (length-1#64-ll) payload [.const 3#64] _ returned leftRead rightRead installed afterCanonical
  have firstNumber : (length-1#64).toNat=length.toNat-1 := by
    rw [BitVec.toNat_sub_of_le (show 1#64≤length from by change 1≤length.toNat; omega)]
    rfl
  have number : (length-1#64-ll).toNat=length.toNat-1-ll.toNat := by
    rw [BitVec.toNat_sub_of_le (show ll≤length-1#64 from by change ll.toNat≤(length-1#64).toNat; rw [firstNumber]; omega),firstNumber]
  rw [number] at bound
  have headerNumber : (1#64+ll).toNat=1+ll.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1+ll.toNat<2^64; omega)]
    rfl
  have read : eval source (.rstruct [.op .add [.const 1#64,localVar "ll"],localVar "n",.const flag])=some (result (1#64+ll) payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,llCell,payloadCell,result,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actual := (Input.return_normal source post _ returned tailRun).1
  have answer : returned=result (1#64+ll) payload flag := (Option.some.inj (read.symm.trans actual)).symm
  refine ⟨1#64+ll,payload,flag,answer,?_,?_,?_,binary,?_⟩
  · rw [headerNumber]; omega
  · rw [headerNumber]; omega
  · rw [headerNumber]; omega
  · intro listFlag
    rw [headerNumber]
    omega

set_option maxRecDepth 10000 in
/-- The actual scoped length-reader result is a checked scalar; the actual
following extent guard bounds it inside the original input length. -/
theorem long_case_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte length base flag : BitVec 64) (llSize : Nat)
    (positive : 0<length.toNat) (small : llSize≤8) (difference : byte-base=BitVec.ofNat 64 llSize)
    (binary : flag=0#64 ∨ flag=1#64)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) : Returns source (longCase base flag) (Valid length.toNat) := by
  have read : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (BitVec.ofNat 64 llSize))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [longCase]
  refine Input.ReturnFacts.declared_word source "ll" _ (BitVec.ofNat 64 llSize) _ (Valid length.toNat) read ?_
  let entered := bind source "ll" (BitVec.ofNat 64 llSize)
  have currentLength : entered.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "ll" "len" _ (by decide)).trans lengthCell
  have currentLl : entered.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) := bind_lookup_same _ _ _
  have llNumber : (BitVec.ofNat 64 llSize).toNat=llSize := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  intro post returned normal
  have leftRead : eval entered (.op .sub [localVar "len",.const 1#64])=some (.val (.word (length-1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval entered (localVar "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) := by simp [eval,evalHOLExact,localVar,toExact,currentLl]
  obtain ⟨extent,scopedRun⟩ := Fail.lower_guard_return entered post _ _ (length-1#64) (BitVec.ofNat 64 llSize) [.const 3#64] _ returned leftRead rightRead installed normal
  have lengthNumber : (length-1#64).toNat=length.toNat-1 := by
    rw [BitVec.toNat_sub_of_le (show 1#64≤length from by change 1≤length.toNat; omega)]
    rfl
  rw [llNumber,lengthNumber] at extent
  obtain ⟨positiveClock,args,actualBody,callee,actualShape,target,actualPayload,inner,argRead,called,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_data entered post "n" .one (ofString "rlp_read_length") readArguments (afterRead flag) returned scopedRun
  have typed : shapeOfHOLExact actualPayload=.one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨payload,payloadEq⟩ := Input.RlpWrite.U256Value.scalar_word actualPayload typed
  rw [payloadEq] at continuationRun
  let ready := Input.CallNormal.continuationEntry entered target "n" (.val (.word payload))
  have readyLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "n" "len" payload (by decide)).trans currentLength
  have readyLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) :=
    (bind_lookup_other _ "n" "ll" payload (by decide)).trans currentLl
  have readyPayload : ready.locals.lookup (ofString "n")=some (.val (.word payload)) := bind_lookup_same _ _ _
  have codes := (Input.evaluation_fields (callEntryStateHOLFinite entered callee) target actualBody (some (.returned actualPayload)) bodyRun).2.2.2
  change target.code=source.code at codes
  have readyInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed target.code; rw [codes]; exact installed
  exact after_read_normal_value ready inner length (BitVec.ofNat 64 llSize) payload flag (by rw [llNumber]; exact small)
    (by rw [llNumber]; omega) binary readyLength readyLl readyPayload readyInstalled returned continuationRun

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.after_read_normal_value
#print axioms InitECandidate.Solver.Rlp.Header.long_case_returns
