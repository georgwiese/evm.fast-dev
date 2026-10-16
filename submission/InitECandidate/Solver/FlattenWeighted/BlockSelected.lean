import InitECandidate.Solver.FlattenWeighted.BlockIf

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm StackSemEvaluate

/-- A conditional evaluates only its selected branch; malformed tests fail
without changing the source state. -/
theorem evaluate_branchChoice {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width) (state : StackSemStateFiniteExact width C F) :
    evaluate (.ite cmp register operand first second, state) =
      match branchChoice cmp register operand state with
      | some true => evaluate (first, state)
      | some false => evaluate (second, state)
      | none => (some .error, state) := by
  cases hx : StackSemStateOps.getVar register state <;>
    cases hy : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) state <;>
    simp [branchChoice, evaluate_ite, hx, hy]
  split <;> simp_all

/-- Branch bounds may use the actual test result as an extra hypothesis. -/
theorem BlockBound.iteCases {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (register : Nat) (operand : HolRegImm width)
    {first second : HolProg width} {pre post : StackSemStateFiniteExact width C F → Prop}
    {credits clocks : Nat}
    (left : BlockBound first
      (fun state => pre state ∧ branchChoice cmp register operand state = some true) post credits clocks)
    (right : BlockBound second
      (fun state => pre state ∧ branchChoice cmp register operand state = some false) post credits clocks) :
    BlockBound (.ite cmp register operand first second) pre post (credits + 1) clocks := by
  constructor
  · intro state valid
    exact Work.ite (fun selected => left.work state ⟨valid, selected⟩)
      (fun selected => right.work state ⟨valid, selected⟩)
  · intro state valid
    rw [evaluate_branchChoice]
    cases selected : branchChoice cmp register operand state with
    | none => simp
    | some value =>
      cases value
      · exact right.clock state ⟨valid, selected⟩
      · exact left.clock state ⟨valid, selected⟩
  · intro state next valid run
    rw [evaluate_branchChoice] at run
    cases selected : branchChoice cmp register operand state with
    | none => simp [selected] at run
    | some value =>
      cases value
      · exact right.normal state next ⟨valid, selected⟩ (by simpa [selected] using run)
      · exact left.normal state next ⟨valid, selected⟩ (by simpa [selected] using run)
  · intro state next valid run
    rw [evaluate_branchChoice] at run
    cases selected : branchChoice cmp register operand state with
    | none => simp [selected] at run
    | some value =>
      cases value
      · exact right.timeout state next ⟨valid, selected⟩ (by simpa [selected] using run)
      · exact left.timeout state next ⟨valid, selected⟩ (by simpa [selected] using run)

private theorem vacuous {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (pre post : StackSemStateFiniteExact width C F → Prop)
    (credits clocks : Nat) (impossible : ∀ state, pre state → False) :
    BlockBound prog pre post credits clocks where
  work := fun state valid => (impossible state valid).elim
  clock := fun state valid => (impossible state valid).elim
  normal := fun state _ valid _ => (impossible state valid).elim
  timeout := fun state _ valid _ => (impossible state valid).elim

/-- A known branch needs no bound for the unreachable alternative. -/
theorem BlockBound.iteSelected {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (register : Nat) (operand : HolRegImm width) (value : Bool)
    {first second : HolProg width} {pre post : StackSemStateFiniteExact width C F → Prop}
    {credits clocks : Nat}
    (selected : ∀ state, pre state → branchChoice cmp register operand state = some value)
    (bound : BlockBound (if value then first else second) pre post credits clocks) :
    BlockBound (.ite cmp register operand first second) pre post (credits + 1) clocks := by
  apply BlockBound.iteCases
  · cases value
    · apply vacuous
      intro state h
      have same := selected state h.1
      simp [h.2] at same
    · exact bound.weaken (fun _ h => h.1) (fun _ h => h) (by omega) (by omega)
  · cases value
    · exact bound.weaken (fun _ h => h.1) (fun _ h => h) (by omega) (by omega)
    · apply vacuous
      intro state h
      have same := selected state h.1
      simp [h.2] at same

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.evaluate_branchChoice
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.iteCases
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.iteSelected
