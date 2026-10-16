import InitECandidate.Solver.WeightedTrace

/-! Ordinary-dispatch guards from a static code region. Keeping these facts
separate avoids importing compiler artifact equality just to locate FFI PCs. -/
namespace InitECandidate.Solver.BootstrapRegion
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Solver

noncomputable def Within (domain : BitVec 64 → Prop) (lo hi : Nat) :
    List (HolAsm 64) → AsmState 64 → Prop
  | [], _ => True
  | i :: rest, s => s.memDomain = domain ∧ lo ≤ s.pc.toNat ∧
      s.pc.toNat + (riscvEnc i).length ≤ hi ∧
      Within domain lo hi rest (WeightedTrace.after s i)

theorem ffi_disjoint (mc : MachineConfig 64 riscv_state RiscVProjection)
    (s : AsmState 64) (length hi : Nat) (nowrap : hi ≤ 2 ^ 64)
    (upper : s.pc.toNat + length ≤ hi)
    (above : ∀ pc ∈ mc.ffiEntryPcs, hi ≤ pc.toNat) :
    ffiEntryPcsDisjoint mc s length := by
  intro address both
  obtain ⟨member, offset, bound, equation⟩ := both
  have far := above address member
  rw [equation] at far
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show s.pc.toNat + offset < 2 ^ 64 by omega)] at far
  omega

/-- A trace inside a known ordinary region has every evaluator guard. -/
theorem guards (mc : MachineConfig 64 riscv_state RiscVProjection)
    (domain : BitVec 64 → Prop) (lo hi : Nat)
    (configured : mc.progAddresses = domain) (nowrap : hi ≤ 2 ^ 64)
    (above : ∀ pc ∈ mc.ffiEntryPcs, hi ≤ pc.toNat)
    (code : List (HolAsm 64)) (s : AsmState 64)
    (region : Within domain lo hi code s) : WeightedTrace.Guards mc code s := by
  induction code generalizing s with
  | nil => trivial
  | cons i rest ih =>
    exact ⟨configured.trans region.1.symm,
      ffi_disjoint mc s (riscvEnc i).length hi nowrap region.2.2.1 above,
      ih _ region.2.2.2⟩

theorem append (domain : BitVec 64 → Prop) (lo hi : Nat)
    (left right : List (HolAsm 64)) (s : AsmState 64) :
    Within domain lo hi (left ++ right) s ↔
      Within domain lo hi left s ∧ Within domain lo hi right (WeightedTrace.run left s) := by
  induction left generalizing s with
  | nil => simp [Within, WeightedTrace.run]
  | cons i rest ih => simp only [List.cons_append, Within, WeightedTrace.run, ih, and_assoc]

end InitECandidate.Solver.BootstrapRegion

#print axioms InitECandidate.Solver.BootstrapRegion.ffi_disjoint
#print axioms InitECandidate.Solver.BootstrapRegion.guards
