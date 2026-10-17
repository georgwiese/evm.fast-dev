import InitECandidate.Solver.Input.OffsetsFaultChecks

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem fault_step {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer current fixed total prior : BitVec 64)
    (index : Nat) (small : index≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : source.memaddrs (pointer+BitVec.ofNat 64 (8*index)))
    (cell : source.memory (pointer+BitVec.ofNat 64 (8*index))=.word current)
    (priorMapped : 0<index→source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (priorCell : 0<index→source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior)
    (bad : (current.toNat<fixed.toNat ∨ total.toNat<current.toNat) ∨ (0<index ∧ current.toNat<prior.toNat))
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    ∃ code : BitVec 64,(code=10#64 ∨ code=11#64) ∧
      evaluateHOLFiniteState source loopBody=
        (some (.exception (ofString "SszErr") (.val (.word code))),
          restore source "o" (emptyLocalsHOLFinite {source with clock:=source.clock-1})) := by
  classical
  let entered:=WitnessRadix.QueryBranch.bind source "o" current
  have address:=cell_address_read source pointer index pointerLocal indexLocal
  have read : eval source (.load .one cellAddress)=some (.val (.word current)) := by
    simp only [eval] at address ⊢
    rw [evalHOLExact,address]
    simp [isWfShapeExactHOL,memLoadHOLExact,mapped,cell]
  have p : entered.locals.lookup (ofString "offs")=some (.val (.word pointer)) :=
    (bind_lookup_other source "o" "offs" current (by decide)).trans pointerLocal
  have i : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other source "o" "i" current (by decide)).trans indexLocal
  have f : entered.locals.lookup (ofString "fixed")=some (.val (.word fixed)) :=
    (bind_lookup_other source "o" "fixed" current (by decide)).trans fixedLocal
  have n : entered.locals.lookup (ofString "len")=some (.val (.word total)) :=
    (bind_lookup_other source "o" "len" current (by decide)).trans totalLocal
  obtain ⟨code,allowed,run⟩:=fault_checks entered pointer current fixed total prior index small p i (bind_lookup_same _ _ _) f n
    priorMapped priorCell bad lookup exceptionShape enough
  have setup : WitnessRadix.BuildEntry.Initializes source [("o",.load .one cellAddress)] entered
      (fun target=>restore source "o" target) := .step current read (.done _)
  have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup checks
  rw [run] at scopeRun
  refine ⟨code,allowed,?_⟩
  rw [loop_body_shape]
  exact scopeRun

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.fault_step
