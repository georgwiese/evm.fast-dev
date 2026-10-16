import InitECandidate.Solver.FlattenBound.Leaves
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.ShMem

/-! Shared-memory flattening retains the zero-extra-clock witness: the source
already consumes the Lab step's clock. All original dispatch guards remain. -/
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

/-- Simulation of a successful-dispatch shared-memory load of size `k`. -/
theorem shMemLoadSim {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemLoad reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hlen : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedRead)
        [BitVec.ofNat 8 k] (panWordToBytesHOL addr false) with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi newBytes => (none, { StackSemStateOps.decClock s1 with
          regs := (StackSemStateOps.decClock s1).regs.updateEq
            (reg, .word (panWordOfBytesHOL false 0 newBytes))
          ffi := newFfi })) = (r, s2)) :
    BoundedConcl limit (.shMemOp op reg (.addr a w) : HolProg width) s1 t r s2 n l cs bs t1 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemLoad reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
          (sharedMemoryWordBytes addr) with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemLoad]
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true]
    cases callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
      (sharedMemoryWordBytes addr) <;> rfl
  rw [panWordToBytes_eq_shared,
    show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with clock := t1.clock + 0 }, Nat.zero_le _, ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with
        ffi := ffi'
        regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs }, Nat.zero_le _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with
          clock := t1.clock + 0 + ck1 - 1
          ffi := ffi'
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1)
        (some (reg, .word (wordOfBytesHOL8 false 0 bytes)))
      simpa [panWordOfBytes_eq_wordOfBytesHOL8, StackSemStateOps.decClock] using this

/-- Simulation of a successful-dispatch shared-memory store of size `k`. -/
theorem shMemStoreSim {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr v : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {payload : List (BitVec 8)}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hv : t1.regs reg = .word v)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemStore reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hpay : payload = (if k = 0 then sharedMemoryWordBytes v
      else (sharedMemoryWordBytes v).take k) ++ sharedMemoryWordBytes addr)
    (hlen : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 k] payload with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi _ => (none, { StackSemStateOps.decClock s1 with ffi := newFfi })) =
        (r, s2)) :
    BoundedConcl limit (.shMemOp op reg (.addr a w) : HolProg width) s1 t r s2 n l cs bs t1 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemStore reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemStore]
    rw [show ({ t1 with clock := c } : Flapjack.Compiler.Backend.LabSem.State width C F).regs reg
      = .word v from hv]
    simp only
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true, ← hpay]
    cases callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload <;> rfl
  rw [show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with clock := t1.clock + 0 }, Nat.zero_le _, ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with
        ffi := ffi'
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs }, Nat.zero_le _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with clock := t1.clock + 0 + ck1 - 1, ffi := ffi', pc := t1.pc + 1 })
        (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1) none
      simpa [StackSemStateOps.decClock] using this

/-- `ShMemOp` case. -/
theorem flattenCorrectShMemOp (s1 : StackSemStateFiniteExact width C F) (op : HolMemop)
    (reg a : Nat) (w : BitVec width) :
    BoundedProp limit (.shMemOp op reg (.addr a w) : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_shMemOp] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have clk := relClock rel
  have ffiEq := relFfi rel
  split at ev
  · rename_i addr hexp
    have haddr : addrValue (.addr a w) t1 = some addr := InstCorrect.addrOfWordExp rel hexp
    split_ifs at ev with h0
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, t1, Nat.zero_le _, fun ck1 => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, ffiEq]
      · omega
    · have cnz : t1.clock ≠ 0 := by omega
      have hlen : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length = 1 := by
        simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
      have good : goodDimindex width := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, g⟩ := rel
        exact g
      have pos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
      have err : ∀ {x : StackSemStateFiniteExact width C F},
          (some StackSemResult.error, x) = (r, s2) → False := fun e => by
        simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
      cases op
      case load =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim limit (k := 0) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom]) hlen ev
        · exact (err ev).elim
      case load8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoadByte] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim limit (k := 1) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad16] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim limit (k := 2) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad32] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim limit (k := 4) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case store =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim limit (k := 0) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStoreByte] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim limit (k := 1) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared, sharedBytesTakeOne v pos]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore16] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim limit (k := 2) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore32] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim limit (k := 4) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.shMemLoadSim
#print axioms InitECandidate.Solver.FlattenBound.shMemStoreSim
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectShMemOp
