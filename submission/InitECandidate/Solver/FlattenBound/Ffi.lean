import InitECandidate.Solver.FlattenBound.Arithmetic
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Ffi

/-! FFI flattening uses the original two-step witness for return-label setup
and dispatch, including both returning and final foreign calls. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack.Compiler.Backend
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
section
variable {width : Nat} [NeZero width] {C F : Type} (limit : Nat)

/-- `FFI` case. -/
theorem flattenCorrectFfi (s1 : StackSemStateFiniteExact width C F)
    (f : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
    BoundedProp limit (.ffi f ptr len ptr2 len2 ret : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_ffi] at ev
  simp only [StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm (.callFFI f) 0 [] 0, .label n l 0] t1.code := by
    simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst
  simp only [isLabelHOL, Bool.false_eq_true, if_false, if_true,
    codeInstalled] at hinst
  obtain ⟨fetch0, fetch1, locL, -⟩ := hinst
  obtain ⟨-, -, hmem, hdom, -, hbe, hffiEq, hclk, -, -, -, hnf, d13, d14, d15, d16, -⟩ := id rel
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  · rename_i w w2 w3 w4 hlen hptr hlen2 hptr2
    have rlen := InstCorrect.regOfLookup rel hlen
    have rptr := InstCorrect.regOfLookup rel hptr
    have rlen2 := InstCorrect.regOfLookup rel hlen2
    have rptr2 := InstCorrect.regOfLookup rel hptr2
    split at ev
    · rename_i cfg bytes hcfg hbytes
      rw [← hmem, ← hdom, ← hbe] at hcfg hbytes
      -- the two LabSem steps from any clock `c + 2`
      have step : ∀ c, evaluate { t1 with clock := c + 2 } =
          match callFFIHOL t1.ffi (.extCall f) cfg bytes with
          | .final outcome => (.halt (.ffiOutcome outcome),
              incPc (decClock (updReg t1.linkReg (.loc n l) { t1 with clock := c + 2 })))
          | .ret newFfi returned => evaluate { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2
              clock := c } := by
        intro c
        rw [evaluate]
        simp only [show c + 2 ≠ 0 by omega, if_false, asmFetch, fetch0, getPcValue, locL,
          reduceCtorEq]
        rw [evaluate]
        simp only [incPc, decClock, updReg, labToLoc, show c + 2 - 1 ≠ 0 by omega, if_false,
          asmFetch, fetch1, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, if_true,
          rlen, rptr, rlen2, rptr2, hcfg, hbytes, locL]
        cases callFFIHOL t1.ffi (.extCall f) cfg bytes with
        | final o => rfl
        | ret newFfi returned =>
          simp only
          congr 1
      rw [← hffiEq] at ev
      split at ev
      · rename_i outcome hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, incPc (decClock (updReg t1.linkReg (.loc n l)
          { t1 with clock := t1.clock + 2 })), (Nat.le_trans (by decide : 2 ≤ 4) (four_le_budget _ _ _ _)), ?_, ?_⟩
        · rw [step, hffi]
        · simp [incPc, decClock, updReg, hffiEq]
      · rename_i newFfi returned hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2 }, (Nat.le_trans (by decide : 2 ≤ 4) (four_le_budget _ _ _ _)), fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
          ?_, ?_⟩
        · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1) + 2 by omega, step, hffi]
        · simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
        · have := stateRelFfiRet rel f t1.linkReg rfl (.loc n l)
            (writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be) newFfi (t1.pc + 2)
          simpa [hmem, hdom, hbe] using this
    · exact (err ev).elim
  · exact (err ev).elim

end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectFfi
