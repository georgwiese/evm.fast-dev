import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step
import InitECandidate.Solver.NopCostTight
import InitECandidate.Solver.BoundedStep

/-! Quantitative simulation of fetched Lab lines. These lemmas retain the full
compiler state relation and handle encoding padding before counting clocks. -/
namespace InitECandidate.Solver.LabCostTight
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend
open InitECandidate.Solver

/-- Simulate the leading instruction `instr` of a fetched line whose bytes
`bytes'` encode it with NOP padding. -/
theorem stepOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (bound : Nat)
    (bounded : EncoderBound.Contract mc.target bound) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length)
      t1).failed) :
    ∃ l ms2, l ≤ bound ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target
        (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, ht1f, -, htpc, -, c43, c44, c45, -⟩ := hrel
  obtain ⟨count, rfl⟩ := (encWithNop_iff _ _ _).mp henc
  have hlen : (mc.target.config.encode instr).length ≤
      (mc.target.config.encode instr ++
        (List.replicate count (mc.target.config.encode (.inst .skip))).flatten).length := by
    simp
  apply EncoderBound.step mc bound bounded t1 ms1 io instr
  refine ⟨hec, c3, ffiEntryPcsDisjoint_shorter mc t1 _ _ ⟨hdis, hlen⟩, c27, ?_, c1⟩
  refine ⟨?_, linkGuard_flip _ _ c43, c44, c45, rfl, hnf, hok⟩
  rw [htpc]
  exact bytesInMem_encWithNop _ _ _ _ _ _ _ henc hmem

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), given that the line's
bytes are still in the target memory after the instruction. -/
theorem stepNopOfLineMem {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (bound : Nat)
    (bounded : EncoderBound.Contract mc.target bound) (nops : NopBound.PaddingContract mc.target) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hb2 : bytesInMemoryHOL t1.pc bytes'
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem t1.memDomain)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, l ≤ bound + bytes'.length / 4 ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  apply NopCostTight.asmStepImpEvaluateStepNop mc bound bounded nops t1 ms1 io instr _ bytes'
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), when the instruction
leaves memory unchanged outside the source memory domain. -/
theorem stepNopOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (bound : Nat)
    (bounded : EncoderBound.Contract mc.target bound) (nops : NopBound.PaddingContract mc.target) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hmemeq : ∀ a, ¬ s1.memDomain a = true →
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem a = t1.mem a)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, l ≤ bound + bytes'.length / 4 ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  have hb2 := bytesInMem_impliesMemory_change _ t1.mem
    (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem _ bytes' _
    (fun a ha => (hmemeq a ha).symm) hmem
  rw [← htpc] at hb2
  apply NopCostTight.asmStepImpEvaluateStepNop mc bound bounded nops t1 ms1 io instr _ bytes'
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

end InitECandidate.Solver.LabCostTight

#print axioms InitECandidate.Solver.LabCostTight.stepOfLine
#print axioms InitECandidate.Solver.LabCostTight.stepNopOfLineMem
#print axioms InitECandidate.Solver.LabCostTight.stepNopOfLine
