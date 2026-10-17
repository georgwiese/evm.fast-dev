import InitECandidate.Solver.Input.HeaderGuards

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact actual decoder entry on arbitrary copied input. All three early
length/schema rejection paths raise real SszErr at one call clock; passing
entry exposes the literal first-container continuation with shifted p/len. -/
theorem entry_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source body=
      if input.length%2^64<2 then
        (some (.exception (ofString "SszErr") (.val (.word 1#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else if Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1 then
        (some (.exception (ofString "SszErr") (.val (.word 2#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else if input.length%2^64<18 then
        (some (.exception (ofString "SszErr") (.val (.word 80#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else evaluateHOLFiniteState (shifted source pointer (input.length%2^64)) afterHeader := by
  classical
  have lengthSmall : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
  have firstRun:=length_guard_execute source (input.length%2^64) 2 1 lengthSmall (by decide) lengthLocal code exceptionShape enough
  by_cases short : input.length%2^64<2
  · simp only [if_pos short] at firstRun ⊢
    rw [entry_shape,WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ firstRun (by change source.clock-1≤source.clock; omega)]
  · simp only [if_neg short] at firstRun ⊢
    rw [entry_shape,WitnessRadix.StateSteps.next_sequence source source _ _ firstRun (Nat.le_refl _)]
    have secondRun:=schema_guard_execute source input pointer heap (by omega) pointerLocal code exceptionShape enough
    by_cases wrong : Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1
    · simp only [if_pos wrong] at secondRun ⊢
      rw [WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ secondRun (by change source.clock-1≤source.clock; omega)]
    · simp only [if_neg wrong] at secondRun ⊢
      rw [WitnessRadix.StateSteps.next_sequence source source _ _ secondRun (Nat.le_refl _)]
      obtain ⟨_,pointerRun,lengthRun⟩:=shift_execute source pointer (input.length%2^64) lengthSmall (by omega) pointerLocal lengthLocal
      let next:=WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)
      let target:=shifted source pointer (input.length%2^64)
      rw [WitnessRadix.StateSteps.next_sequence source next _ _ pointerRun (Nat.le_refl _),
        WitnessRadix.StateSteps.next_sequence next target _ _ lengthRun (Nat.le_refl _)]
      have thirdRun:=length_guard_execute target (input.length%2^64-2) 16 80 (by omega) (by decide)
        (bind_lookup_same _ _ _) code exceptionShape enough
      by_cases small : input.length%2^64<18
      · simp only [if_pos small]
        have bad : input.length%2^64-2<16 := by omega
        simp only [if_pos bad] at thirdRun
        rw [WitnessRadix.StateSteps.stopped_sequence target _ _ _ _ thirdRun (by change source.clock-1≤source.clock; omega)]
        rfl
      · simp only [if_neg small]
        have valid : ¬input.length%2^64-2<16 := by omega
        simp only [if_neg valid] at thirdRun
        rw [WitnessRadix.StateSteps.next_sequence target target _ _ thirdRun (Nat.le_refl _)]

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.entry_execute
