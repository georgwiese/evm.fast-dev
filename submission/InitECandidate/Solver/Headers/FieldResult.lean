import InitECandidate.Solver.Headers.FieldResultSyntax
import InitECandidate.Solver.Headers.FieldFrame

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The whole original helper derives its returned string slice from the
real item decoder, rather than accepting a supplied future header result. -/
theorem body_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length cursor limit : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    ∃ header payload,Rlp.Item.Valid pointer length.toNat (Rlp.Item.result pointer header payload 0#64) ∧ value=kind.returnValue (pointer+header) payload := by
  rw [body_shape] at normal
  obtain ⟨funded,parsed,header,payload,flag,inner,valid,nextArena,above,domain,endian,code,heap,cost,continued,endpoint⟩ :=
    Rlp.Item.scoped_normal_above source post pointer length cursor limit "it" arguments kind.afterItem args arena fits installed value normal
  let ready := Input.CallNormal.continuationEntry source parsed "it" (Rlp.Item.result pointer header payload flag)
  have cell : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨zero,valueEq⟩ := after_item_normal_value ready inner kind pointer header payload flag cell value continued
  subst flag
  exact ⟨header,payload,valid,valueEq⟩

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.after_item_shape
#print axioms InitECandidate.Solver.Headers.Field.checks_pure
#print axioms InitECandidate.Solver.Headers.Field.after_item_normal_value
#print axioms InitECandidate.Solver.Headers.Field.body_normal_value
