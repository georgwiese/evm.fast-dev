import InitECandidate.Solver.Input.OffsetsChecks

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem valid_checks {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer current fixed total prior : BitVec 64)
    (index : Nat) (small : index≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (currentLocal : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (lower : fixed.toNat≤current.toNat) (upper : current.toNat≤total.toNat)
    (priorMapped : 0<index→source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (priorCell : 0<index→source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior)
    (ordered : 0<index→prior.toNat≤current.toNat) :
    evaluateHOLFiniteState source checks=(none,WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 (index+1))) := by
  classical
  have rangeRead:=range_read source current fixed total currentLocal fixedLocal totalLocal
  have notBad : ¬(current.toNat<fixed.toNat ∨ total.toNat<current.toNat) := by omega
  simp only [if_neg notBad,eval] at rangeRead
  have rangeRun : evaluateHOLFiniteState source rangeGuard=(none,source) := by
    rw [rangeGuard,evaluateHOLFiniteState_ite,rangeRead]
    simp
  have previousRead:=has_previous_read source index small indexLocal
  simp only [eval] at previousRead
  have orderRun : evaluateHOLFiniteState source orderGuard=(none,source) := by
    by_cases positive : 0<index
    · simp only [if_pos positive] at previousRead
      have orderRead:=order_read source pointer current prior index pointerLocal indexLocal currentLocal (priorMapped positive) (priorCell positive)
      have notBefore : ¬current.toNat<prior.toNat := by have:=ordered positive; omega
      simp only [if_neg notBefore,eval] at orderRead
      rw [orderGuard,evaluateHOLFiniteState_ite,previousRead]
      simp only [show (1#64 : BitVec 64)≠0 from by decide,↓reduceIte]
      rw [evaluateHOLFiniteState_ite,orderRead]
      simp
    · simp only [if_neg positive] at previousRead
      rw [orderGuard,evaluateHOLFiniteState_ite,previousRead]
      simp
  have nextRead : eval source (addConst (localVar "i") 1#64)=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,indexLocal,valueIsWord,valueWord,
      wordOpHOL,wordOp,BitVec.ofNat_add]
  have incrementRun:=WitnessRadix.StateSteps.assign_execute source "i" _ (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index+1)) indexLocal nextRead
  rw [checks,WitnessRadix.StateSteps.next_sequence source source _ _ rangeRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence source source _ _ orderRun (Nat.le_refl _)]
  exact incrementRun

/-- One literal successful offset-validation body, including its current-word
load, both guards, local increment and lexical restoration. -/
theorem valid_step {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer current fixed total prior : BitVec 64)
    (index : Nat) (small : index≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : source.memaddrs (pointer+BitVec.ofNat 64 (8*index)))
    (cell : source.memory (pointer+BitVec.ofNat 64 (8*index))=.word current)
    (lower : fixed.toNat≤current.toNat) (upper : current.toNat≤total.toNat)
    (priorMapped : 0<index→source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (priorCell : 0<index→source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior)
    (ordered : 0<index→prior.toNat≤current.toNat) :
    evaluateHOLFiniteState source loopBody=(none,WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 (index+1))) := by
  classical
  let entered:=WitnessRadix.QueryBranch.bind source "o" current
  have address:=cell_address_read source pointer index pointerLocal indexLocal
  have read : eval source (.load .one cellAddress)=some (.val (.word current)) := by
    simp only [eval] at address ⊢
    rw [evalHOLExact,address]
    simp [toExact,isWfShapeExactHOL,memLoadHOLExact,mapped,cell]
  have p : entered.locals.lookup (ofString "offs")=some (.val (.word pointer)) :=
    (bind_lookup_other source "o" "offs" current (by decide)).trans pointerLocal
  have i : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other source "o" "i" current (by decide)).trans indexLocal
  have f : entered.locals.lookup (ofString "fixed")=some (.val (.word fixed)) :=
    (bind_lookup_other source "o" "fixed" current (by decide)).trans fixedLocal
  have n : entered.locals.lookup (ofString "len")=some (.val (.word total)) :=
    (bind_lookup_other source "o" "len" current (by decide)).trans totalLocal
  have run:=valid_checks entered pointer current fixed total prior index small p i (bind_lookup_same _ _ _) f n
    lower upper priorMapped priorCell ordered
  have setup : WitnessRadix.BuildEntry.Initializes source [("o",.load .one cellAddress)] entered
      (fun target=>restore source "o" target) := .step current read (.done _)
  have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup checks
  rw [run] at scopeRun
  rw [loop_body_shape]
  change evaluateHOLFiniteState source (WitnessRadix.BuildEntry.declarations [("o",.load .one cellAddress)] checks)=_
  rw [scopeRun]
  change (none,restore source "o" (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "o" current) "i" (BitVec.ofNat 64 (index+1))))=_
  rw [restore_bind_other source (WitnessRadix.QueryBranch.bind source "o" current) "o" "i" _ (by decide),restore_bound source "o" current]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.valid_checks
#print axioms InitECandidate.Solver.Input.Offsets.valid_step
