#!/usr/bin/env python3
"""Retain costs in the pinned generic NOP-padded ASM simulation."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'.lake/packages/flapjack/Flapjack/Compiler/Backend/LabToTarget/NopSteps.lean'
s=p.read_text(); start=s.index('/-- Wrapped address reassociation;'); s=s[start:]
s=s.replace('end Flapjack.Compiler.Backend.LabToTarget','end InitECandidate.Solver.NopCost')
s='''import Flapjack.Compiler.Backend.LabToTarget.NopSteps
import InitECandidate.Solver.EncoderBound

/-! Quantitative NOP padding, adapted from the pinned simulation. All original
memory, interference and source-step premises are retained. -/
namespace InitECandidate.Solver.NopCost
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabToTarget
open InitECandidate.Solver

'''+s
s=s.replace('(c : MachineConfig width S Q)\n    (h :','(c : MachineConfig width S Q) (bound : Nat) (bounded : EncoderBound.Contract c.target bound)\n    (h :',1)
s=s.replace('(c : MachineConfig width S Q) (s1 : AsmState width) (ms1 : S) (io : HolFfiState σ)', '(c : MachineConfig width S Q) (bound : Nat) (bounded : EncoderBound.Contract c.target bound)\n    (s1 : AsmState width) (ms1 : S) (io : HolFfiState σ)',1)
s=s.replace('∃ l ms2, ∀ k,','∃ l ms2, l ≤ bound * n ∧ ∀ k,',1)
s=s.replace('∃ l ms2, ∀ k,','∃ l ms2, l ≤ bound * (bytes.length + 1) ∧ ∀ k,',1)
s=s.replace('refine ⟨0, ms1, fun k => ?_⟩','refine ⟨0, ms1, by simp, fun k => ?_⟩')
s=s.replace('asmStepImpEvaluate c s1 ms1 io', 'EncoderBound.step c bound bounded s1 ms1 io')
s=s.replace('obtain ⟨l, ms2, hl⟩ := hstep','obtain ⟨l, ms2, small, hl⟩ := hstep')
s=s.replace('ms2 (shiftInterfer l c)\n', 'ms2 (shiftInterfer l c) bounded\n',1)
s=s.replace("obtain ⟨l', ms3, hl'⟩ := ih'", "obtain ⟨l', ms3, small', hl'⟩ := ih'")
s=s.replace("refine ⟨l + l', ms3, fun k => ?_⟩", "refine ⟨l + l', ms3, by rw [Nat.mul_succ]; omega, fun k => ?_⟩",1)
s=s.replace('obtain ⟨l, ms2, hl⟩ := EncoderBound.step','obtain ⟨l, ms2, small, hl⟩ := EncoderBound.step')
s=s.replace('refine ⟨l, ms2, fun k => ?_⟩','refine ⟨l, ms2, small.trans (Nat.le_mul_of_pos_right _ (by omega)), fun k => ?_⟩')
s=s.replace("obtain ⟨l', ms3, hl'⟩ := evaluateNopSteps io n s ms2 (shiftInterfer l c)", "obtain ⟨l', ms3, small', hl'⟩ := evaluateNopSteps io n s ms2 (shiftInterfer l c) bound bounded")
s=s.replace("  refine ⟨l + l', ms3, fun k => ?_⟩", '''  have skipPositive : 0 < skip.length := by
    apply List.length_pos_iff.mpr
    exact encOkNotEmpty c.target.config (.inst .skip) ⟨henc.1.1, asmOk_skip _⟩
  have paddingLe : n ≤ (enc ++ (List.replicate n skip).flatten).length := by
    have mul := Nat.le_mul_of_pos_right n skipPositive
    rw [hblen]
    omega
  have wholeBound := Nat.mul_le_mul_left bound (Nat.add_le_add_right paddingLe 1)
  refine ⟨l + l', ms3, ?_, fun k => ?_⟩
  · simp only [Nat.mul_add, Nat.mul_one] at wholeBound ⊢
    omega''')
s+='\n#print axioms InitECandidate.Solver.NopCost.evaluateNopSteps\n#print axioms InitECandidate.Solver.NopCost.asmStepImpEvaluateStepNop\n'
(root/'submission/InitECandidate/Solver/NopCost.lean').write_text(s)
