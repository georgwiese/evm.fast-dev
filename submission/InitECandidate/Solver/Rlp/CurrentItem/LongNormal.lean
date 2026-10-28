import InitECandidate.Solver.Rlp.CurrentItem.LongReturn
import InitECandidate.Solver.Rlp.CurrentItem.CasePrices

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem long_case_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte base flag : BitVec 64) (llSize : Nat)
    (entry : Entry source pointer length)
    (small : llSize≤8) (difference : byte-base=BitVec.ofNat 64 llSize) (binary : flag=0#64 ∨ flag=1#64)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (longCase base flag)=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  have read : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (BitVec.ofNat 64 llSize))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [longCase] at normal
  obtain ⟨declaredInner,declaredRun,declaredRestore⟩ := Input.declaration_return_word source post "ll" _ (BitVec.ofNat 64 llSize) _ value read normal
  let entered := bind source "ll" (BitVec.ofNat 64 llSize)
  have enteredEntry : Entry entered pointer length := Entry.bound_word source pointer length (BitVec.ofNat 64 llSize) "ll" entry (by decide) (by decide)
  have llCell : entered.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) := bind_lookup_same _ _ _
  have llNumber : (BitVec.ofNat 64 llSize).toNat=llSize := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have leftRead : eval entered (.op .sub [localVar "len",.const 1#64])=some (.val (.word (length-1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,enteredEntry.lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval entered (localVar "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) := by simp [eval,evalHOLExact,localVar,toExact,llCell]
  obtain ⟨extent,scopedRun⟩ := Fail.lower_guard_return entered declaredInner _ _ (length-1#64) (BitVec.ofNat 64 llSize) [.const 3#64] _ value leftRead rightRead installed declaredRun
  have lengthNumber : (length-1#64).toNat=length.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact entry.nonempty)
  rw [llNumber,lengthNumber] at extent
  have args : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) Header.readArguments=some (ReadLength.values (pointer+1#64) llSize) := by
    simp [Header.readArguments,ReadLength.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,enteredEntry.pointerCell,llCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := ReadLength.environment entered.code.lookup (pointer+1#64) llSize (ReadLength.original_code entered.code installed)
  obtain ⟨positive,calleePost,returned,inner,bodyRun,checked,continuation,restored⟩ := Input.CallNormal.scoped_normal entered declaredInner "n" .one (ofString "rlp_read_length") Header.readArguments _ ReadLength.body (afterRead flag) callee .one args called value scopedRun
  have fields := ReadLength.readonly entered.code installed (callEntryStateHOLFinite entered callee) rfl
  rw [bodyRun] at fields
  change Input.LocalEffects.erase calleePost=Input.LocalEffects.erase entered at fields
  have typed : shapeOfHOLExact returned=.one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨payload,payloadEq⟩ := Input.scalar_word_of_shape returned typed
  rw [payloadEq] at continuation
  let ready := bind {calleePost with locals:=entered.locals} "n" payload
  have readyEntry : Entry ready pointer length := Entry.readonly_resume entered calleePost pointer length "n" (.val (.word payload)) enteredEntry fields (by decide) (by decide)
  have readyLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llSize))) :=
    (bind_lookup_other _ "n" "ll" _ (by decide)).trans llCell
  have codeEq := congrArg PanSemStateFiniteExact.code fields
  change ready.code=entered.code at codeEq
  obtain ⟨valid,nextArena⟩ := after_read_normal ready inner pointer length (BitVec.ofNat 64 llSize) payload flag readyEntry
    (by rw [llNumber]; exact small) (by rw [llNumber]; have := entry.nonempty; omega) binary readyLl (bind_lookup_same _ _ _)
    (by rw [codeEq]; exact installed) value continuation
  refine ⟨valid,?_⟩
  · rw [declaredRestore,restored]
    exact nextArena.trans fields

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.long_case_normal
