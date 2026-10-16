import InitECandidate.Solver.GuestWork.ZeroMemory
import InitECandidate.Solver.FlattenWeighted.BasicClock

namespace InitECandidate.Solver.GuestWork.ZeroMemory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions StackSemControl
open Flapjack.Compiler.Encoders.Asm
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Clears {C F : Type} (prog : HolProg 64) : Prop :=
  ∀ source : StackSemStateFiniteExact 64 C F, Below (evaluate (prog, source)).2.memory source.memory

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

theorem seqAt {C F : Type} (first second : HolProg 64) (source : StackSemStateFiniteExact 64 C F)
    (a : Below (evaluate (first, source)).2.memory source.memory)
    (b : Clears (C := C) (F := F) second) :
    Below (evaluate (.seq first second, source)).2.memory source.memory := by
  rw [seqEvaluate]
  rcases run : evaluate (first, source) with ⟨result, next⟩
  rw [run] at a
  cases result with
  | none => exact a.trans (b next)
  | some _ => exact a

theorem Clears.seq {C F : Type} {first second : HolProg 64}
    (a : Clears (C := C) (F := F) first) (b : Clears (C := C) (F := F) second) : Clears (C := C) (F := F) (.seq first second) :=
  fun source => seqAt first second source (a source) b

theorem Clears.ite {C F : Type} (cmp : Cmp) (reg : Nat) (operand : HolRegImm 64)
    {first second : HolProg 64} (a : Clears (C := C) (F := F) first)
    (b : Clears (C := C) (F := F) second) : Clears (C := C) (F := F) (.ite cmp reg operand first second) := by
  intro source
  rw [evaluate_ite]
  repeat' split
  all_goals first | exact a source | exact b source | exact Below.refl _

theorem Clears.loop {C F : Type} {body : HolProg 64}
    (bodyClears : Clears (C := C) (F := F) body) : Clears (C := C) (F := F) (.loop body) := by
  have all : ∀ n (source : StackSemStateFiniteExact 64 C F), source.clock = n →
      Below (evaluate (.loop body, source)).2.memory source.memory := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro source ranked
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
      rcases run : evaluate (body, source) with ⟨result, next⟩
      have a := bodyClears source
      rw [run] at a
      have clockLe := StackSemEvaluateClock.evaluateClock body source result next run
      by_cases continues : contLoop result = true
      · simp only [continues, if_true]
        by_cases zero : next.clock = 0
        · simpa [zero, emptyEnv] using a
        · simp only [zero, if_false]
          exact a.trans (ih (decClock next).clock (by simp only [decClock]; omega) (decClock next) rfl)
      · simpa [continues] using a
  intro source
  exact all source.clock source rfl

def noStoreInst : HolInst 64 → Bool
  | .skip | .const _ _ | .arith _ => true
  | _ => false

private theorem instructionMemory {C F : Type} (instruction : HolInst 64)
    (supported : noStoreInst instruction = true)
    (source post : StackSemStateFiniteExact 64 C F)
    (execution : StackSemInst.instHOL instruction source = some post) : post.memory = source.memory := by
  cases instruction <;> simp only [noStoreInst] at supported
  all_goals try contradiction
  all_goals simp only [StackSemInst.instHOL, instInteger, Option.join_some] at execution
  all_goals repeat' split at execution
  all_goals try simp only [assign] at execution
  all_goals repeat' split at execution
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at execution
  all_goals cases execution
  all_goals rfl

def noStoreLeaf : HolProg 64 → Bool
  | .inst instruction => noStoreInst instruction
  | .skip | .tick | .ret _ | .halt _ | .break _ | .continue _ | .locValue _ _ _ => true
  | _ => false

theorem Clears.leaf {C F : Type} (prog : HolProg 64) (supported : noStoreLeaf prog = true) :
    Clears (C := C) (F := F) prog := by
  intro source
  cases prog with
  | inst instruction =>
    rw [evaluate_inst]
    cases run : StackSemInst.instHOL instruction source with
    | none => exact Below.refl _
    | some post =>
      have same := instructionMemory instruction supported source post run
      simpa only [same] using Below.refl source.memory
  | skip => simpa [evaluate_skip] using Below.refl source.memory
  | tick => rw [evaluate_tick]; split <;> exact Below.refl _
  | ret reg => rw [evaluate_ret]; split <;> exact Below.refl _
  | halt reg => rw [evaluate_halt]; split <;> exact Below.refl _
  | «break» label => simpa [evaluate_break] using Below.refl source.memory
  | «continue» label => simpa [evaluate_continue] using Below.refl source.memory
  | locValue reg label offset => rw [evaluate_locValue]; split <;> exact Below.refl _
  | _ => simp [noStoreLeaf] at supported

/-- A skip inserted after the first block does not change the memory summary. -/
theorem Clears.skipAfter {C F : Type} {first rest : HolProg 64}
    (h : Clears (C := C) (F := F) (.seq first rest)) : Clears (C := C) (F := F) (.seq first (.seq .skip rest)) := by
  intro source
  have same : evaluate (.seq first (.seq .skip rest), source) = evaluate (.seq first rest, source) := by
    simp only [seqEvaluate, evaluate_skip]
  rw [same]
  exact h source

end InitECandidate.Solver.GuestWork.ZeroMemory
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.seqAt
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.seq
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.ite
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.loop
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.leaf
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.skipAfter
