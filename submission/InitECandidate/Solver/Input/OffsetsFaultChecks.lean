import InitECandidate.Solver.Input.OffsetsChecks

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Either actual failing per-offset guard raises its real decoder exception;
no increment or later guard resumes, and the sole call costs one source clock. -/
theorem fault_checks {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer current fixed total prior : BitVec 64)
    (index : Nat) (small : index≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (currentLocal : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (priorMapped : 0<index→source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (priorCell : 0<index→source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior)
    (bad : (current.toNat<fixed.toNat ∨ total.toNat<current.toNat) ∨ (0<index ∧ current.toNat<prior.toNat))
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    ∃ code : BitVec 64,(code=10#64 ∨ code=11#64) ∧
      evaluateHOLFiniteState source checks=
        (some (.exception (ofString "SszErr") (.val (.word code))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
  classical
  have rangeRead:=range_read source current fixed total currentLocal fixedLocal totalLocal
  by_cases badRange : current.toNat<fixed.toNat ∨ total.toNat<current.toNat
  · simp only [if_pos badRange,eval] at rangeRead
    have failed:=SszFail.call_execute source 10#64 lookup exceptionShape enough
    have guardRun : evaluateHOLFiniteState source rangeGuard=
        (some (.exception (ofString "SszErr") (.val (.word 10#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
      rw [rangeGuard,evaluateHOLFiniteState_ite,rangeRead]
      simpa [fail] using failed
    refine ⟨10#64,Or.inl rfl,?_⟩
    rw [checks,WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ guardRun (by change source.clock-1≤source.clock; omega)]
  · obtain ⟨positive,before⟩:=bad.resolve_left badRange
    simp only [if_neg badRange,eval] at rangeRead
    have rangeRun : evaluateHOLFiniteState source rangeGuard=(none,source) := by
      rw [rangeGuard,evaluateHOLFiniteState_ite,rangeRead]
      simp
    have hasPrior:=has_previous_read source index small indexLocal
    have orderRead:=order_read source pointer current prior index pointerLocal indexLocal currentLocal (priorMapped positive) (priorCell positive)
    simp only [if_pos positive,eval] at hasPrior
    simp only [if_pos before,eval] at orderRead
    have failed:=SszFail.call_execute source 11#64 lookup exceptionShape enough
    have orderRun : evaluateHOLFiniteState source orderGuard=
        (some (.exception (ofString "SszErr") (.val (.word 11#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
      rw [orderGuard,evaluateHOLFiniteState_ite,hasPrior]
      simp only [↓reduceIte]
      rw [evaluateHOLFiniteState_ite,orderRead]
      simpa [fail] using failed
    refine ⟨11#64,Or.inr rfl,?_⟩
    rw [checks,WitnessRadix.StateSteps.next_sequence source source _ _ rangeRun (Nat.le_refl _),
      WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ orderRun (by change source.clock-1≤source.clock; omega)]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.fault_checks
