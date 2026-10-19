import InitECandidate.Solver.Rlp.ItemValue
import InitECandidate.Solver.Rlp.CanonicalReturn
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem short_return_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (shortReturn flag)=(some (.returned value),post)) :
    value=result pointer 1#64 payload flag := by
  have read : eval source (.rstruct [.const flag,.op .add [localVar "p",.const 1#64],localVar "n",.op .add [.const 1#64,localVar "n"]])=
      some (result pointer 1#64 payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,pointerCell,payloadCell,result,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact Option.some.inj ((Input.return_normal source post _ value normal).1.symm.trans read)

theorem long_return_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer ll payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (longReturn flag)=(some (.returned value),post)) :
    value=result pointer (1#64+ll) payload flag := by
  have read : eval source (.rstruct [.const flag,.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n",.op .add [.const 1#64,localVar "ll",localVar "n"]])=
      some (result pointer (1#64+ll) payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,pointerCell,llCell,payloadCell,result,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  exact Option.some.inj ((Input.return_normal source post _ value normal).1.symm.trans read)

private theorem count_locals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_list_count") arguments)=(none,post)) : post.locals=source.locals := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,same,_⟩ := Input.CallNormal.ignored_data source post (ofString "rlp_list_count") arguments normal
  rw [same]

/-- The optional nested list validation retains real caller locals; no
future list-count result or arena model is needed to identify this return. -/
theorem long_tail_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer ll payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (longTail flag)=(some (.returned value),post)) :
    value=result pointer (1#64+ll) payload flag := by
  rw [longTail] at normal
  by_cases zero : flag=0#64
  · rw [if_pos zero] at normal
    exact long_return_value source post pointer ll payload flag pointerCell llCell payloadCell value normal
  · rw [if_neg zero] at normal
    obtain ⟨middle,countRun,returnRun⟩ := Input.sequence_returned source post longCount (longReturn flag) value (Input.NoReturn.ignored_call _ _ source) normal
    have locals := count_locals source middle _ countRun
    exact long_return_value middle post pointer ll payload flag (by rw [locals]; exact pointerCell)
      (by rw [locals]; exact llCell) (by rw [locals]; exact payloadCell) value returnRun

theorem short_string_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer byte : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortString=(some (.returned value),post)) : value=result pointer 1#64 (byte-128#64) 0#64 := by
  have read : eval source (.op .sub [localVar "b",.const 128#64])=some (.val (.word (byte-128#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_string_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (byte-128#64) _ value read normal
  let entered := bind source "n" (byte-128#64)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (byte-128#64))) := bind_lookup_same _ _ _
  obtain ⟨guardRun,tailRun⟩ := Fail.guard_return entered inner _ [.const 3#64] (.seq Header.canonicalGuard (shortReturn 0#64)) value installed innerRun
  have returnRun := Header.canonical_return entered inner (byte-128#64) payloadCell (shortReturn 0#64) value installed tailRun
  exact short_return_value entered inner pointer (byte-128#64) 0#64
    ((bind_lookup_other _ "n" "p" _ (by decide)).trans pointerCell) payloadCell value returnRun

theorem short_list_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer byte : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortList=(some (.returned value),post)) : value=result pointer 1#64 (byte-192#64) 1#64 := by
  have read : eval source (.op .sub [localVar "b",.const 192#64])=some (.val (.word (byte-192#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_list_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (byte-192#64) _ value read normal
  let entered := bind source "n" (byte-192#64)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (byte-192#64))) := bind_lookup_same _ _ _
  obtain ⟨guardRun,tailRun⟩ := Fail.guard_return entered inner _ [.const 3#64] (.seq shortCount (shortReturn 1#64)) value installed innerRun
  obtain ⟨middle,countRun,returnRun⟩ := Input.sequence_returned entered inner shortCount (shortReturn 1#64) value (Input.NoReturn.ignored_call _ _ entered) tailRun
  have locals := count_locals entered middle _ countRun
  exact short_return_value middle inner pointer (byte-192#64) 1#64
    (by rw [locals]; exact (bind_lookup_other _ "n" "p" _ (by decide)).trans pointerCell) (by rw [locals]; exact payloadCell) value returnRun

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.short_return_value
#print axioms InitECandidate.Solver.Rlp.Item.long_return_value
#print axioms InitECandidate.Solver.Rlp.Item.long_tail_value
#print axioms InitECandidate.Solver.Rlp.Item.short_string_encoding
#print axioms InitECandidate.Solver.Rlp.Item.short_list_encoding
