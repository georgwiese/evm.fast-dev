import InitECandidate.Solver.LabCost
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Common

/-! A bounded Lab-to-target simulation for static programs. Dynamic code
installation is excluded explicitly, rather than assigned an unjustified cost. -/
namespace InitECandidate.Solver.LabBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.AsmProps
open InitECandidate.Solver

/-- Adjacent encoded source positions bound each fetched target line. -/
def LineBound {width : Nat} [NeZero width] (code : LabProgHOL width) (limit : Nat) : Prop :=
  ∀ pc, posVal (pc + 1) 0 code ≤ posVal pc 0 code + limit

/-- No source position invokes dynamic code installation. -/
def NoInstall {width : Nat} [NeZero width] (code : LabProgHOL width) : Prop :=
  ∀ pc w bytes n, asmFetchAux pc code ≠ some (.labAsm .install w bytes n)

def rate (bound limit : Nat) : Nat := bound * (limit + 1) + 2

theorem base_le (bound limit : Nat) : bound + 1 ≤ rate bound limit := by
  have h := Nat.le_mul_of_pos_right bound (show 0 < limit + 1 by omega)
  unfold rate
  omega

theorem terminal_bound {clock cost : Nat} (bound limit : Nat)
    (positive : clock ≠ 0) (small : cost ≤ bound) :
    clock + cost ≤ rate bound limit * clock := by
  have rateBig := base_le bound limit
  have h := Nat.mul_le_mul_right clock rateBig
  have h' := Nat.le_mul_of_pos_right bound (show 0 < clock by omega)
  simp only [Nat.add_mul, Nat.one_mul] at h
  omega

theorem recursive_bound {clock extra prefixCost : Nat} (bound limit : Nat)
    (positive : clock ≠ 0)
    (tail : clock - 1 + extra ≤ rate bound limit * (clock - 1))
    (head : prefixCost ≤ rate bound limit) (nonzero : prefixCost ≠ 0) :
    clock + (extra + prefixCost - 1) ≤ rate bound limit * clock := by
  have equation : clock = (clock - 1) + 1 := by omega
  have expanded : rate bound limit * clock =
      rate bound limit * (clock - 1) + rate bound limit := by
    conv_lhs => rw [equation, Nat.mul_add, Nat.mul_one]
  rw [expanded]
  omega

theorem padded_le {width : Nat} [NeZero width] {code : LabProgHOL width}
    {limit count pc : Nat} (bound : Nat) (lines : LineBound code limit)
    (position : posVal (pc + 1) 0 code = posVal pc 0 code + count) :
    bound * (count + 1) ≤ rate bound limit := by
  have line := lines pc
  have small : count ≤ limit := by omega
  have h := Nat.mul_le_mul_left bound (Nat.add_le_add_right small 1)
  unfold rate
  omega

def BoundedCorrect {width : Nat} [NeZero width] (S Q : Type) {F : Type}
    (bound limit : Nat) (s1 : LabSem.State width Config F) : Prop :=
  ∀ (res : MachineResult) (mc : MachineConfig width S Q) (s2 : LabSem.State width Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (p : BitVec width),
    EncoderBound.Contract mc.target bound → LineBound code2 limit → NoInstall s1.code →
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrect mc.target ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 →
    ∃ k ms2, s1.clock + k ≤ rate bound limit * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi)

theorem compileCorrect_step {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 s1' s2 : LabSem.State width Config F} {t1' : AsmState width}
    {ms1 ms2 : S} {res : MachineResult} {l bound limit : Nat}
    (bounded : EncoderBound.Contract mc.target bound) (lines : LineBound code2 limit)
    (static : NoInstall s1.code) (small : l ≤ rate bound limit)
    (sameCode : s1'.code = s1.code)
    (ht : oracleTie mc ms1 s1) (hec : encoderCorrect mc.target) (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL (shiftInterfer l mc) s1.ffi k ms2 ∧
      findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hs' : s1'.clock = s1.clock - 1 ∧ s1'.ffi = s1.ffi ∧ s1'.ioRegs = s1.ioRegs ∧
      s1'.ioFpRegs = s1.ioFpRegs ∧ s1'.ccRegs = s1.ccRegs ∧ s1'.ccFpRegs = s1.ccFpRegs)
    (hrel' : stateRel (shiftInterfer l mc, code2, labs, p) s1' t1' ms2)
    (hev : evaluate s1' = (res, s2)) (hres : res ≠ .error)
    (ih : BoundedCorrect S Q bound limit s1') :
    ∃ k ms3, s1.clock + k ≤ rate bound limit * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨hc, hffi, hio, hiofp, hcc, hccfp⟩ := hs'
  have ht' : oracleTie (shiftInterfer l mc) ms2 s1' :=
    oracleTie_step mc ms1 ms2 s1 s1' l ⟨ht, fun k => (hl k).2, hio, hiofp, hcc, hccfp, hffi⟩
  obtain ⟨k', ms3, upper, hk⟩ := ih res (shiftInterfer l mc) s2 code2 labs t1' ms2 p
    bounded lines (sameCode ▸ static) ⟨ht', hev, hres, hec, hrel'⟩
  have clockEq : s1.clock = s1'.clock + 1 := by omega
  refine ⟨k' + l - 1, ms3, ?_, ?_⟩
  · rw [clockEq, Nat.mul_add, Nat.mul_one]
    omega
  · rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, (hl _).1, ← hffi]
    exact hk

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.compileCorrect_step
