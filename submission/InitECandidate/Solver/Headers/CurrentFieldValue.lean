import InitECandidate.Solver.Headers.CurrentFieldMemory
import InitECandidate.Solver.Headers.FieldResultSyntax
import InitECandidate.Solver.Headers.FieldChecks

namespace InitECandidate.Solver.Headers.CurrentField
open Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- The actual field return identifies its contained string payload and
real return value. No successful future parser or supplied output is assumed. -/
theorem body_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    ∃ header payload,Rlp.Item.Valid pointer length.toNat (Rlp.Item.result pointer header payload 0#64) ∧ value=kind.returnValue (pointer+header) payload := by
  rw [Field.body_shape] at normal
  obtain ⟨answer,itemPost,inner,valid,forward,price,frame,continued,endpoint⟩:=Rlp.CurrentItem.scoped_normal source post pointer length arena fits "it" arguments kind.afterItem args value normal
  obtain ⟨header,payload,flag,same,small,positive,bounded,binary,listHeader⟩:=valid
  subst answer
  let ready:=setVarHOLFinite (ofString "it") (Rlp.Item.result pointer header payload flag) {itemPost with locals:=source.locals}
  have cell : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨zero,valueEq⟩:=after_item_normal_value ready inner kind pointer header payload flag cell value continued
  subst flag
  exact ⟨header,payload,⟨header,payload,0#64,rfl,small,positive,bounded,binary,listHeader⟩,valueEq⟩

end InitECandidate.Solver.Headers.CurrentField

#print axioms InitECandidate.Solver.Headers.CurrentField.body_normal_value
