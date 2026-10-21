import InitECandidate.Solver.Headers.DecodeSlices
import InitECandidate.Solver.Rlp.DecodeReturnedTrace
import InitECandidate.Solver.Input.LiteralGuardNormal

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine whole-header return forces the original kind guard to pass
and supplies the actual complete list and reached slicing continuation. -/
theorem top_kind_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ parsed header payload inner,
      Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64) ∧
      evaluateHOLFiniteState (topState source parsed pointer header payload) afterKind=(some (.returned value),inner) ∧
      post=restore source "top" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) topArguments=some (Rlp.Header.values pointer length) := by
    simp [topArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape] at run
  obtain ⟨parsed,answer,inner,returned,remaining,endpoint⟩ := Rlp.Decode.scoped_returned source post pointer length cursor limit "top" topArguments afterTop args arena fits installed value run
  obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := returned.complete
  subst answer
  let ready:=Input.CallNormal.continuationEntry source parsed "top" (Rlp.Item.result pointer header payload flag)
  have topCell : ready.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have read : eval ready (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))=some (.val (.word (if flag≠1#64 then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change evaluateHOLFiniteState ready afterTop=(some (.returned value),inner) at remaining
  rw [after_top_shape.1] at remaining
  obtain ⟨passed,continued⟩ := Input.literal_guard_normal ready inner _ (ofString "HdrErr") 10#64 (flag≠1#64) read afterKind value remaining
  have one : flag=1#64 := by simpa using passed
  subst flag
  exact ⟨parsed,header,payload,inner,returned,continued,endpoint⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.top_kind_returned
