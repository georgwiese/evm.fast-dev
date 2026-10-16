import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement

/-! Clock accounting for Stack flattening. Structural work counts exclude the
magnitudes of operands/registers; source clock alone does not count straight-line
work. This module states a strengthened simulation, not its recursive proof. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack.Compiler.Backend
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled

/-- Number of syntax nodes, independent of numeric operand magnitudes. -/
def nodes {width : Nat} [NeZero width] : HolProg width → Nat
  | .seq first second => 1 + nodes first + nodes second
  | .ite _ _ _ first second => 1 + nodes first + nodes second
  | .loop body => 1 + nodes body
  | .call ret _ handler => 1 +
      (match ret with | none => 0 | some (body, _, _, _) => nodes body) +
      (match handler with | none => 0 | some (body, _, _) => nodes body)
  | _ => 1

theorem nodes_positive {width : Nat} [NeZero width] (p : HolProg width) :
    1 ≤ nodes p := by
  cases p <;> try (simp [nodes] <;> omega)
  case call ret dest handler =>
    rcases ret with _ | ⟨body, link, l1, l2⟩ <;>
      rcases handler with _ | ⟨body, l1, l2⟩ <;> simp [nodes] <;> omega

/-- Extra target clocks: a candidate invariant for the recursive flattening
proof. `limit` will bound callee/body syntax sizes, and spent source clock pays
for repeated entries. No theorem here claims the invariant for all programs. -/
def budget {width : Nat} [NeZero width] (limit : Nat) (p : HolProg width)
    (initial final : Nat) : Nat := 4 * ((limit + 1) * (initial - final) + nodes p)

theorem one_le_budget {width : Nat} [NeZero width] (limit : Nat) (p : HolProg width)
    (initial final : Nat) : 1 ≤ budget limit p initial final := by
  have := nodes_positive p
  unfold budget
  omega

theorem budget_seq {width : Nat} [NeZero width] (limit : Nat) (p q : HolProg width)
    (initial middle final a b : Nat) (firstClock : middle ≤ initial)
    (secondClock : final ≤ middle)
    (first : a ≤ budget limit p initial middle)
    (second : b ≤ budget limit q middle final) :
    a + b ≤ budget limit (.seq p q) initial final := by
  have spent : initial - final = (initial - middle) + (middle - final) := by omega
  simp only [budget, nodes, spent, Nat.mul_add] at *
  omega

def BoundedConcl {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    ck ≤ budget limit prog s1.clock s2.clock ∧
    match haltView r with
    | some res => evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
    | none =>
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      match r.map (fun w => resultView w n cs bs) with
      | none =>
        t2.pc = t1.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t prog n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2
      | some (.vloc n1 n2) =>
        (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
          ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
      | some (.vcont n1 n2) =>
        stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
      | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
      | some .verr => False


def BoundedProp {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
    FlattenHyps prog s1 t r s2 n l cs bs t1 →
    BoundedConcl limit prog s1 t r s2 n l cs bs t1

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.nodes_positive
#print axioms InitECandidate.Solver.FlattenBound.budget_seq
