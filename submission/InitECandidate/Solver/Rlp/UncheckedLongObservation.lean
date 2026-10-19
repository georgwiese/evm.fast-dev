import InitECandidate.Solver.Rlp.UncheckedControl
import InitECandidate.Solver.Rlp.HeaderEncoding

namespace InitECandidate.Solver.Rlp.Unchecked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem long_case_observed (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer b base : BitVec 64) (llName nName : String)
    (llOther : ofString llName≠ofString "p") (namesOther : ofString nName≠ofString llName)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (longCase base llName nName)=(some (.returned value),post)) :
    ∃ payload : BitVec 64,ReadLength.Observed source (pointer+1#64) (b-base) payload ∧
      value=.val (.word (1#64+(b-base)+payload)) := by
  have llRead : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (b-base))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [longCase] at normal
  obtain ⟨declaredPost,declaredRun,declaredRestore⟩ :=
    Input.declaration_return_word source post llName _ (b-base) _ value llRead normal
  let entered := bind source llName (b-base)
  have enteredPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ llName "p" _ llOther).trans pointerCell
  have enteredLength : entered.locals.lookup (ofString llName)=some (.val (.word (b-base))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h:=fun query=>Classical.propDecidable (entered.memaddrs query))
      [.op .add [localVar "p",.const 1#64],localVar llName]=some (ReadLength.values (pointer+1#64) (b-base).toNat) := by
    simp only [ReadLength.values,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,enteredPointer,
      enteredLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨paid,payload,inner,positive,funded,observed,continuation,restored⟩ :=
    ReadLength.scoped_observed entered declaredPost (pointer+1#64) (b-base) nName _ _ value args installed declaredRun
  let ready := bind {entered with clock:=entered.clock-paid} nName payload
  have readyLength : ready.locals.lookup (ofString llName)=some (.val (.word (b-base))) :=
    (bind_lookup_other _ nName llName _ namesOther).trans enteredLength
  have readyPayload : ready.locals.lookup (ofString nName)=some (.val (.word payload)) := bind_lookup_same _ _ _
  have expected : eval ready (.op .add [.const 1#64,localVar llName,localVar nName])=
      some (.val (.word (1#64+(b-base)+payload))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,readyLength,readyPayload,
      valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  have actual := (Input.return_normal ready inner _ value continuation).1
  have same : value=.val (.word (1#64+(b-base)+payload)) := Option.some.inj (actual.symm.trans expected)
  exact ⟨payload,ReadLength.Observed.transport entered source _ _ _ observed (by intro offset inside; rfl),same⟩

end InitECandidate.Solver.Rlp.Unchecked

#print axioms InitECandidate.Solver.Rlp.Unchecked.long_case_observed
