import InitECandidate.Solver.Rlp.HeaderEncoding
import InitECandidate.Solver.Rlp.HeaderShortValues

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem long_case_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer b base flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (longCase base flag)=(some (.returned value),post)) :
    ∃ payload : BitVec 64, ReadLength.Observed source (pointer+1#64) (b-base) payload ∧
      value=result (1#64+(b-base)) payload flag := by
  have llRead : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (b-base))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [longCase] at normal
  obtain ⟨declaredPost,declaredRun,declaredRestore⟩ :=
    Input.declaration_return_word source post "ll" _ (b-base) _ value llRead normal
  let entered := bind source "ll" (b-base)
  have enteredPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "ll" "p" _ (by decide)).trans pointerCell
  have enteredLength : entered.locals.lookup (ofString "ll")=some (.val (.word (b-base))) := bind_lookup_same _ _ _
  obtain ⟨guardRun,scopedRun⟩ := Fail.guard_return entered declaredPost
    (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "ll")) [.const 3#64]
    (.decCall (ofString "n") .one (ofString "rlp_read_length") readArguments (afterRead flag)) value installed declaredRun
  have args : evalListHOLFinite entered (h:=fun query=>Classical.propDecidable (entered.memaddrs query)) readArguments=
      some (ReadLength.values (pointer+1#64) (b-base).toNat) := by
    simp only [ReadLength.values,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp [readArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
      enteredPointer,enteredLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨paid,payload,inner,positive,funded,observed,continuation,restored⟩ :=
    ReadLength.scoped_observed entered declaredPost (pointer+1#64) (b-base) "n" readArguments (afterRead flag) value args installed scopedRun
  let ready := bind {entered with clock:=entered.clock-paid} "n" payload
  have readyLength : ready.locals.lookup (ofString "ll")=some (.val (.word (b-base))) :=
    (bind_lookup_other _ "n" "ll" _ (by decide)).trans enteredLength
  have readyPayload : ready.locals.lookup (ofString "n")=some (.val (.word payload)) := bind_lookup_same _ _ _
  obtain ⟨canonicalRun,afterCanonical⟩ := Fail.guard_return ready inner
    (.cmp .notLower (.const 55#64) (localVar "n")) [.const 5#64] _ value installed continuation
  obtain ⟨extentRun,tailRun⟩ := Fail.guard_return ready inner
    (.cmp .lower (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"]) (localVar "n")) [.const 3#64]
    (.return (.rstruct [.op .add [.const 1#64,localVar "ll"],localVar "n",.const flag])) value installed afterCanonical
  have expected : eval ready (.rstruct [.op .add [.const 1#64,localVar "ll"],localVar "n",.const flag])=
      some (result (1#64+(b-base)) payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,readyLength,readyPayload,result,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actual := (Input.return_normal ready inner _ value tailRun).1
  exact ⟨payload,observed,Option.some.inj (actual.symm.trans expected)⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.long_case_encoding
