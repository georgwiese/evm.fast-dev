import InitECandidate.Solver.Rlp.CanonicalReturn
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem short_string_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (b : BitVec 64) (byteCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortString=(some (.returned value),post)) :
    value=result 1#64 (b-128#64) 0#64 := by
  have payloadRead : eval source (.op .sub [localVar "b",.const 128#64])=some (.val (.word (b-128#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_string_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (b-128#64) _ value payloadRead normal
  let entered := bind source "n" (b-128#64)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (b-128#64))) := bind_lookup_same _ _ _
  obtain ⟨guardRun,tailRun⟩ := Fail.guard_return entered inner
    (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "n")) [.const 3#64]
    (.seq canonicalGuard (shortReturn 0#64)) value installed innerRun
  have returnRun := canonical_return entered inner (b-128#64) payloadCell (shortReturn 0#64) value installed tailRun
  exact short_return_value entered inner (b-128#64) 0#64 value payloadCell returnRun

theorem short_list_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (b : BitVec 64) (byteCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortList=(some (.returned value),post)) :
    value=result 1#64 (b-192#64) 1#64 := by
  have payloadRead : eval source (.op .sub [localVar "b",.const 192#64])=some (.val (.word (b-192#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_list_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (b-192#64) _ value payloadRead normal
  let entered := bind source "n" (b-192#64)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (b-192#64))) := bind_lookup_same _ _ _
  obtain ⟨guardRun,tailRun⟩ := Fail.guard_return entered inner
    (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "n")) [.const 3#64]
    (shortReturn 1#64) value installed innerRun
  exact short_return_value entered inner (b-192#64) 1#64 value payloadCell tailRun

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.short_string_encoding
#print axioms InitECandidate.Solver.Rlp.Header.short_list_encoding
