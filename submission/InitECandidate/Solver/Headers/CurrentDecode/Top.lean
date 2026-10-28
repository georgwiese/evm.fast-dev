import InitECandidate.Solver.Headers.DecodeSyntax
import InitECandidate.Solver.Rlp.CurrentDecodeCall
import InitECandidate.Solver.Input.LiteralGuardNormal

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- The real header decoder first derives a complete list item and passes
its literal kind check. The actual later slicing continuation is retained. -/
theorem top_kind_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header payload : BitVec 64,∃ clock : Nat,∃ inner,
      Rlp.CurrentDecode.Complete pointer length (Rlp.Item.result pointer header payload 1#64) ∧ clock≤source.clock ∧ source.clock-clock≤46*length.toNat+13 ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {source with clock:=clock}) afterKind=(some (.returned value),inner) ∧
      post=restore source "top" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) topArguments=some (Rlp.Header.values pointer length) := by
    simp [topArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape] at run
  obtain ⟨answer,clock,inner,complete,forward,price,remaining,endpoint⟩:=Rlp.CurrentDecode.scoped_normal source post pointer length arena fits "top" topArguments afterTop args value run
  obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩:=complete
  subst answer
  let ready:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload flag) {source with clock:=clock}
  have topCell : ready.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have read : eval ready (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))=some (.val (.word (if flag≠1#64 then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change evaluateHOLFiniteState ready afterTop=(some (.returned value),inner) at remaining
  rw [after_top_shape.1] at remaining
  obtain ⟨passed,continued⟩:=literal_guard_normal ready inner _ (ofString "HdrErr") 10#64 (flag≠1#64) read afterKind value remaining
  have one : flag=1#64 := by simpa using passed
  subst flag
  exact ⟨header,payload,clock,inner,⟨header,payload,1#64,rfl,small,positive,extent,binary,listHeader⟩,forward,price,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.top_kind_returned
