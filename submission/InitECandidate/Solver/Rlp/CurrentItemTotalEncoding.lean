import InitECandidate.Solver.Rlp.HeaderCallEncoding
import InitECandidate.Solver.Rlp.ItemTotalProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Rlp.CurrentItemTotal
open ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal item-total return retains its validated input encoding.
This provenance comes from the actual header callee; nested validation is
only required to preserve the caller's header binding before the return. -/
theorem body_encoding (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ header payload flag : BitVec 64, Header.Valid length.toNat (Header.result header payload flag) ∧
      Header.Encoded source pointer header payload flag ∧ value=.val (.word (header+payload)) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨paid,header,payload,flag,inner,minimum,maximum,funded,valid,encoding,continuation,restored⟩ :=
    Header.scoped_normal_encoding source target pointer length "h" arguments afterHeader args installed value (by rw [←body_shape]; exact normal)
  let ready := setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have headerCell : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have safe : Input.LocalPrefix (ofString "h") check := by
    unfold check validate
    exact .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,checkRun,returnRun,headerPreserved⟩ := safe.normal_continue ready inner (.return total) value continuation
  have currentHeader : middle.locals.lookup (ofString "h")=some (Header.result header payload flag) := headerPreserved.trans headerCell
  have expected : eval middle total=some (.val (.word (header+payload))) := by
    simp [total,eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentHeader,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actual := (Input.return_normal middle inner total value returnRun).1
  exact ⟨header,payload,flag,valid,encoding,Option.some.inj (actual.symm.trans expected)⟩

end InitECandidate.Solver.Rlp.CurrentItemTotal

#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.body_encoding
