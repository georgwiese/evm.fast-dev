import InitECandidate.Solver.FlattenBound.StateInvariant

/-! Subprogram invariants and the bounded induction hypothesis used to close
the recursive flattening proof. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

def BoundedIH {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ p' s', MeasureLt p' s' p s → ProgramOk limit p' → StateOk limit s' →
    BoundedProp limit p' s'

theorem programOk_seq {width : Nat} [NeZero width] (limit : Nat)
    (p q : HolProg width) (ok : ProgramOk limit (.seq p q)) :
    ProgramOk limit p ∧ ProgramOk limit q := by
  simp only [ProgramOk, nodes, StackProps.noInstall, Bool.and_eq_true] at ok ⊢
  exact ⟨⟨by omega, ok.2.1⟩, ⟨by omega, ok.2.2⟩⟩

theorem programOk_if {width : Nat} [NeZero width] (limit : Nat)
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width) (p q : HolProg width)
    (ok : ProgramOk limit (.ite cmp reg ri p q)) :
    ProgramOk limit p ∧ ProgramOk limit q := by
  simp only [ProgramOk, nodes, StackProps.noInstall, Bool.and_eq_true] at ok ⊢
  exact ⟨⟨by omega, ok.2.1⟩, ⟨by omega, ok.2.2⟩⟩

theorem programOk_loop {width : Nat} [NeZero width] (limit : Nat)
    (p : HolProg width) (ok : ProgramOk limit (.loop p)) : ProgramOk limit p := by
  simp only [ProgramOk, nodes, StackProps.noInstall] at ok ⊢
  exact ⟨by omega, ok.2⟩

theorem programOk_return {width : Nat} [NeZero width] (limit : Nat)
    (p : HolProg width) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ok : ProgramOk limit (.call (some (p, link, l1, l2)) dest handler)) :
    ProgramOk limit p := by
  rcases handler with _ | ⟨body, a, b⟩
  · simp only [ProgramOk, nodes, StackProps.noInstall, Bool.and_true] at ok ⊢
    exact ⟨by omega, ok.2⟩
  · simp only [ProgramOk, nodes, StackProps.noInstall, Bool.and_eq_true] at ok ⊢
    exact ⟨by omega, ok.2.1⟩

theorem programOk_handler {width : Nat} [NeZero width] (limit : Nat)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Nat ⊕ Nat)
    (p : HolProg width) (l1 l2 : Nat)
    (ok : ProgramOk limit (.call ret dest (some (p, l1, l2)))) :
    ProgramOk limit p := by
  rcases ret with _ | ⟨body, link, a, b⟩
  · simp only [ProgramOk, nodes, StackProps.noInstall, Bool.true_and] at ok ⊢
    exact ⟨by omega, ok.2⟩
  · simp only [ProgramOk, nodes, StackProps.noInstall, Bool.and_eq_true] at ok ⊢
    exact ⟨by omega, ok.2.2⟩

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.programOk_seq
#print axioms InitECandidate.Solver.FlattenBound.programOk_return
#print axioms InitECandidate.Solver.FlattenBound.programOk_handler
