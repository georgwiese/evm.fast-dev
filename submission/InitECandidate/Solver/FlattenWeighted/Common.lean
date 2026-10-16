import InitECandidate.Solver.FlattenBound.Common

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open InitECandidate.Solver.FlattenBound

/-- An explicit execution budget with the original flattening conclusion.
Credits are supplied by a source-work derivation, never by assuming a target run. -/
def PaidConcl {width : Nat} [NeZero width] {C F : Type}
    (credits : Nat) (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    ck ≤ 4 * credits ∧
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


def PaidProp {width : Nat} [NeZero width] {C F : Type}
    (credits : Nat) (prog : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (tail : Bool) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (name label : Nat) (continues breaks : List Nat) (target : LabSem.State width C F),
    FlattenHyps prog source tail result post name label continues breaks target →
    PaidConcl credits prog source tail result post name label continues breaks target

theorem paidOfBounded {width : Nat} [NeZero width] {C F : Type}
    {limit credits : Nat} {prog : HolProg width} {source post : StackSemStateFiniteExact width C F}
    {tail : Bool} {result : Option (StackSemResult width)} {name label : Nat}
    {continues breaks : List Nat} {target : LabSem.State width C F}
    (bound : budget limit prog source.clock post.clock ≤ 4 * credits)
    (checked : BoundedConcl limit prog source tail result post name label continues breaks target) :
    PaidConcl credits prog source tail result post name label continues breaks target := by
  obtain ⟨extra, final, small, conclusion⟩ := checked
  exact ⟨extra, final, Nat.le_trans small bound, conclusion⟩

theorem paidMono {width : Nat} [NeZero width] {C F : Type}
    {first second : Nat} {prog : HolProg width} {source post : StackSemStateFiniteExact width C F}
    {tail : Bool} {result : Option (StackSemResult width)} {name label : Nat}
    {continues breaks : List Nat} {target : LabSem.State width C F}
    (bound : first ≤ second)
    (checked : PaidConcl first prog source tail result post name label continues breaks target) :
    PaidConcl second prog source tail result post name label continues breaks target := by
  obtain ⟨extra, final, small, conclusion⟩ := checked
  exact ⟨extra, final, Nat.le_trans small (Nat.mul_le_mul_left 4 bound), conclusion⟩

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.paidOfBounded
#print axioms InitECandidate.Solver.FlattenWeighted.paidMono
