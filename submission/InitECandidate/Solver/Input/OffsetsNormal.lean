import InitECandidate.Solver.Input.OffsetsAnyExecute

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Invert an actual normal return of the complete fixed validator. No offset
range, ordering or first-offset equality is assumed. -/
theorem normal_first {F : Type} (source post : PanSemStateFiniteExact 64 F) (pointer fixed total : BitVec 64)
    (values : Nat→BitVec 64) (count : Nat) (positive : 0<count) (small : count≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (values position))
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : count+1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ values 0=fixed := by
  obtain ⟨result,target,paid,execution,bound,frame,outcome⟩:=any_execute source pointer fixed total values count positive small
    pointerLocal countLocal fixedLocal totalLocal mapped cells lookup exceptionShape enough
  have equal:=run.symm.trans execution
  have resultEqual:some (.returned value)=result:=congrArg Prod.fst equal
  rcases outcome with normal|fault
  · have valueEqual:=resultEqual.trans normal.1
    cases valueEqual
    exact ⟨rfl,normal.2⟩
  · obtain ⟨code,allowed,exception⟩:=fault
    rw [exception] at resultEqual
    cases resultEqual

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.normal_first
