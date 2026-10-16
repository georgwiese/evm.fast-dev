import Flapjack.Compiler.Backend.Semantics.TargetProps.AsmStepEvaluate

/-! Quantitative adaptation of pinned Flapjack AsmStepEvaluate.lean
(034bb5a1ed0b757082768d5406206bd2f8e31b7c). Keep the assertion counter
explicit all the way into evaluateTargetHOL, including interference and search.
Only targetOk and this instruction's exact assertion proof are needed. -/
namespace InitECandidate.Solver.EncoderClock
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- The original encoder assertion contract, with its counter exposed. The
number of native/evaluator transitions is n+1, not n. -/
def EncoderAt {width : Nat} [NeZero width] {S Q : Type}
    (t : HolAsmTarget width S Q) (s1 s2 : AsmState width) (ms : S)
    (i : HolAsm width) (n : Nat) : Prop :=
  ∀ env : Nat → S → S, interferenceOk env (t.proj s1.memDomain) →
    let pcs := allPcs (t.config.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (t.next s)) ms
      (fun ms' => t.stateOk ms' = true ∧
        (∀ pc, pc ∈ pcs 0 → t.getByte ms' pc = t.getByte ms pc) ∧
        t.getPc ms' ∈ pcs t.config.codeAlignment)
      (fun ms' => targetStateRel t s2 ms') ∧
    asserts2 (n + 1) (fun k => env (n + 1 - k)) t.next ms
      (fun before after => ∀ x, ¬ s1.memDomain x →
        t.getByte before x = t.getByte after x)

/-- An exact encoder assertion yields an exact evaluator prefix. The result
retains the original evaluator and interference-search equality for every tail
clock, rather than merely a raw native state iteration. -/
theorem evaluator_exact {width : Nat} [NeZero width] {S Q σ : Type}
    (c : MachineConfig width S Q) (s1 s2 : AsmState width) (ms1 : S)
    (io : HolFfiState σ) (i : HolAsm width) (n : Nat)
    (hok : targetOk c.target)
    (hdm : c.progAddresses = s1.memDomain)
    (hdis : ffiEntryPcsDisjoint c s1 (c.target.config.encode i).length)
    (hinter : interferenceOk c.nextInterfer (c.target.proj s1.memDomain))
    (hstep : asmStep c.target.config s1 i s2)
    (hrel : targetStateRel c.target s1 ms1)
    (hs : EncoderAt c.target s1 s2 ms1 i n)
    (hnon : c.target.config.encode i ≠ []) :
    ∃ ms2, ∀ k,
      evaluateTargetHOL c io (k + (n + 1)) ms1 =
        evaluateTargetHOL (shiftInterfer (n + 1) c) io k ms2 ∧
      findNextInterference c io (k + (n + 1)) ms1 =
        findNextInterference (shiftInterfer (n + 1) c) io k ms2 ∧
      targetStateRel c.target s2 ms2 ∧ n + 1 ≠ 0 := by
  have hlen : 0 < (c.target.config.encode i).length := by
    exact List.length_pos_iff.mpr hnon
  have hbytes : bytesInMemoryHOL s1.pc (c.target.config.encode i) (c.target.getByte ms1)
      (fun a => c.progAddresses a ∧ a ∉ c.ffiEntryPcs) := by
    apply bytesInMemory_diff s1.pc _ (c.target.getByte ms1) _ s1.memDomain
      (fun a => a ∈ c.ffiEntryPcs)
    refine ⟨?_, ?_, hdis⟩
    · rw [hdm]
    · apply bytesInMemory_changeMem s1.pc _ s1.mem _ s1.memDomain
      refine ⟨hstep.1, ?_⟩
      intro j hj
      apply (hrel.2.2.1 _ ?_).symm
      have hd := bytesInMemory_allPcs _ _ _ _ 0 hstep.1
      apply hd
      rw [allPcs_eq]
      exact ⟨j, by simpa using hj, by simp⟩
  have hnormal : c.progAddresses (c.target.getPc ms1) ∧ c.target.getPc ms1 ∉ c.ffiEntryPcs := by
    have hd := bytesInMemory_allPcs _ _ _ _ 0 hbytes
    apply hd
    rw [allPcs_eq, hrel.2.1]
    exact ⟨0, by simpa using hlen, by simp⟩
  have ha : ∀ env, interferenceOk env (c.target.proj s1.memDomain) →
      asserts n (fun k s => env k (c.target.next s)) ms1
        (fun ms => c.target.stateOk ms = true ∧
          (∀ pc, pc ∈ allPcs (c.target.config.encode i).length s1.pc 0 →
            c.target.getByte ms pc = c.target.getByte ms1 pc) ∧
          c.target.getPc ms ∈ allPcs (c.target.config.encode i).length s1.pc c.target.config.codeAlignment)
        (fun ms => targetStateRel c.target
          s2 ms) := by
    intro env he
    have ht := (hs (fun k => env (n - k)) (fun k ms => he (n - k) ms)).1
    apply asserts_weaken n _ _ ms1 _ _ _ _ ht
    intro k hk
    constructor
    · funext ms
      have hidx : n - (n - k) = k := by omega
      simp only [hidx]
    · exact fun hx => hx
  have hobs : ∀ ms ms', c.target.proj s1.memDomain ms = c.target.proj s1.memDomain ms' →
      c.target.stateOk ms = c.target.stateOk ms' ∧ c.target.getPc ms = c.target.getPc ms' ∧
      ∀ a, s1.memDomain a → c.target.getByte ms a = c.target.getByte ms' a := by
    intro ms ms' hp
    exact (hok.2 ms ms' s1 hp).2
  obtain ⟨ms2, hout⟩ := evaluateEqEvaluate_all n ms1 c io s1.memDomain i s1.pc _
    ⟨hnormal, hrel.1, hdm, hinter, fun _ _ hr => hr.1, hobs, ha,
      (hs c.nextInterfer hinter).2, 0, by simpa using hrel.2.1,
      by simpa using hlen, hbytes⟩
  refine ⟨ms2, ?_⟩
  intro k
  exact ⟨(hout k).1, (hout k).2.1, (hout k).2.2, by omega⟩

end InitECandidate.Solver.EncoderClock

#print axioms InitECandidate.Solver.EncoderClock.evaluator_exact
