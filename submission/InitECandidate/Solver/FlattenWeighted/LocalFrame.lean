import InitECandidate.Solver.FlattenWeighted.BasicFrame
import InitECandidate.Solver.FlattenWeighted.LoopFrame

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps

/-- A local fragment preserving a register and code on every non-timeout exit.
Halts and calls are excluded; loops and both word/byte stores are supported. -/
def keepsLocal {width : Nat} [NeZero width] (reg : Nat) : HolProg width → Bool
  | .seq first second | .ite _ _ _ first second => keepsLocal reg first && keepsLocal reg second
  | .loop body => keepsLocal reg body
  | .inst instruction => keepsInst reg instruction
  | .locValue dest _ _ => decide (dest ≠ reg)
  | .skip | .tick | .ret _ | .break _ | .continue _ => true
  | _ => false

theorem localFrame {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (reg : Nat) (supported : keepsLocal reg prog = true)
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : evaluate (prog, source) = (result, post)) (notTimeout : result ≠ some .timeOut) :
    post.regs.lookup reg = source.regs.lookup reg ∧ post.code = source.code := by
  cases prog with
  | seq first second =>
    have both : keepsLocal reg first = true ∧ keepsLocal reg second = true := by simpa [keepsLocal] using supported
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at execution
    rcases run : evaluate (first, source) with ⟨firstResult, middle⟩
    rw [run] at execution
    cases firstResult with
    | none =>
      have a := localFrame first reg both.1 source middle none run (by simp)
      have b := localFrame second reg both.2 middle post result execution notTimeout
      exact ⟨b.1.trans a.1, b.2.trans a.2⟩
    | some outcome =>
      obtain ⟨rfl, rfl⟩ := execution
      exact localFrame first reg both.1 source _ _ run notTimeout
  | ite cmp register operand first second =>
    have both : keepsLocal reg first = true ∧ keepsLocal reg second = true := by simpa [keepsLocal] using supported
    rw [evaluate_ite] at execution
    repeat' split at execution
    all_goals first
      | exact localFrame first reg both.1 source post result execution notTimeout
      | exact localFrame second reg both.2 source post result execution notTimeout
      | (obtain ⟨rfl, rfl⟩ := execution; exact ⟨rfl, rfl⟩)
  | loop body =>
    have preserved := loopFrame body
      (fun state : StackSemStateFiniteExact width C F => (state.regs.lookup reg, state.code))
      (fun _ => rfl) (fun state nt => by
        rcases run : evaluate (body, state) with ⟨outcome, next⟩
        rw [run] at nt
        exact Prod.ext
          (localFrame body reg supported state next outcome run nt).1
          (localFrame body reg supported state next outcome run nt).2)
      source (by rw [execution]; exact notTimeout)
    rw [execution] at preserved
    exact ⟨congrArg Prod.fst preserved, congrArg Prod.snd preserved⟩
  | inst instruction =>
    rw [evaluate_inst] at execution
    cases run : StackSemInst.instHOL instruction source with
    | none =>
      simp only [run] at execution
      obtain ⟨rfl, rfl⟩ := execution
      exact ⟨rfl, rfl⟩
    | some next =>
      simp only [run] at execution
      obtain ⟨rfl, rfl⟩ := execution
      exact instFrame instruction reg supported source _ run
  | skip =>
    simp only [evaluate_skip] at execution
    obtain ⟨rfl, rfl⟩ := execution
    exact ⟨rfl, rfl⟩
  | tick =>
    rw [evaluate_tick] at execution
    split at execution
    · obtain ⟨rfl, rfl⟩ := execution; exact (notTimeout rfl).elim
    · obtain ⟨rfl, rfl⟩ := execution; exact ⟨rfl, rfl⟩
  | ret register =>
    rw [evaluate_ret] at execution
    split at execution
    all_goals obtain ⟨rfl, rfl⟩ := execution; exact ⟨rfl, rfl⟩
  | locValue dest label offset =>
    simp [keepsLocal] at supported
    rw [evaluate_locValue] at execution
    split at execution
    all_goals obtain ⟨rfl, rfl⟩ := execution
    all_goals simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm supported]
  | «break» label =>
    simp only [evaluate_break] at execution
    obtain ⟨rfl, rfl⟩ := execution
    exact ⟨rfl, rfl⟩
  | «continue» label =>
    simp only [evaluate_continue] at execution
    obtain ⟨rfl, rfl⟩ := execution
    exact ⟨rfl, rfl⟩
  | _ => simp [keepsLocal] at supported
termination_by sizeOf prog

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.localFrame
