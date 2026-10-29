import InitECandidate.Solver.Mpt.LeafInsertDispatch
import InitECandidate.Solver.Mpt.CommonPrefixCall
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original split scope obtains its bounded prefix from the
real comparison call and preserves all nonlocal state before branch creation. -/
theorem prefix_entry_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (left oldLength right length : BitVec 64)
    (small : length.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (oldLengthCell : source.locals.lookup (ofString "el")=some (.val (.word oldLength)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source splitScope=(some (.returned value),target)) :
    ∃ ready inner,∃ prefixLength : BitVec 64,prefixLength.toNat≤min oldLength.toNat length.toNat ∧
      ready.locals.lookup (ofString "pl")=some (.val (.word prefixLength)) ∧
      ready.locals=source.locals.update (ofString "pl",.val (.word prefixLength)) ∧
      Input.LocalEffects.erase ready=Input.LocalEffects.erase source ∧ source.clock-ready.clock≤length.toNat+2 ∧
      evaluateHOLFiniteState ready afterPrefix=(some (.returned value),inner) ∧ target=restore source "pl" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) prefixArguments=
      some (CommonPrefix.values left oldLength right length):=by
    simp [prefixArguments,CommonPrefix.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,oldLengthCell,rightCell,lengthCell]
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=CommonPrefix.environment source.code.lookup left oldLength right length (CommonPrefix.original_code source.code installed)
  rw [dispatch_shapes.2.2.2.2.2] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "pl" .one (ofString "common_prefix_length") prefixArguments _
    CommonPrefix.body afterPrefix callee .one args called value normal
  obtain ⟨prefixLength,answer,bound,cost,frame⟩:=CommonPrefix.body_normal (callEntryStateHOLFinite source callee) child oldLength length
    (Nat.le_trans (Nat.min_le_right _ _) small) installed alCell blCell returned run
  let ready:=Input.CallNormal.continuationEntry source child "pl" returned
  have clockEq : ready.clock=child.clock:=rfl
  have price : source.clock-ready.clock≤length.toNat+2:=by
    change source.clock-1-child.clock≤min oldLength.toNat length.toNat+1 at cost
    rw [clockEq]
    have shorter:=Nat.min_le_right oldLength.toNat length.toNat
    omega
  refine ⟨ready,inner,prefixLength,bound,?_,?_,frame,price,continued,endpoint⟩
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.prefix_entry_normal
