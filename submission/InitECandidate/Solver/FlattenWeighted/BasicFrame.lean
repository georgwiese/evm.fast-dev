import InitECandidate.Solver.FlattenWeighted.BasicClock

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions

/-- Integer instruction fragment with no write to the protected register. -/
def keepsInst {width : Nat} [NeZero width] (reg : Nat) : HolInst width → Bool
  | .skip => true
  | .const dest _ | .arith (.binop _ dest _ _) | .arith (.shift _ dest _ _) => decide (dest ≠ reg)
  | .mem .load dest _ => decide (dest ≠ reg)
  | .mem .store _ _ => true
  | _ => false

private theorem instFrame {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (reg : Nat) (supported : keepsInst reg instruction = true)
    (source post : StackSemStateFiniteExact width C F)
    (execution : StackSemInst.instHOL instruction source = some post) :
    post.regs.lookup reg = source.regs.lookup reg ∧ post.code = source.code := by
  cases instruction with
  | skip =>
    have equal : source = post := by simpa [StackSemInst.instHOL, instInteger] using execution
    subst post
    exact ⟨rfl, rfl⟩
  | const dest value =>
    simp [keepsInst] at supported
    simp only [StackSemInst.instHOL, instInteger, assign] at execution
    repeat' split at execution
    all_goals
      try simp only [Option.join, Option.bind, id, Option.some.injEq] at execution
      first | contradiction | (subst post; subst_vars; simp_all [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm supported])
  | arith arith =>
    cases arith <;> simp only [keepsInst] at supported
    all_goals try contradiction
    all_goals
      simp only [StackSemInst.instHOL, instInteger, assign] at execution
      repeat' split at execution
      all_goals
        try simp only [Option.join, Option.bind, id, Option.some.injEq] at execution
        first | contradiction | (subst post; subst_vars; simp_all [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne_comm])
  | mem op dest addr =>
    cases addr
    cases op <;> simp only [keepsInst] at supported
    all_goals try contradiction
    all_goals
      simp only [StackSemInst.instHOL, instInteger, memStore] at execution
      repeat' split at execution
      all_goals
        try simp only [Option.join, Option.bind, id, Option.some.injEq] at execution
        first | contradiction | (subst post; subst_vars; simp_all [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne_comm])

    all_goals
      rcases ‹_ ∧ _› with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩

/-- The check concerns normal completion only: a halt or return never reaches
the next block. Memory validity is not assumed; failures stop execution. -/
def keepsReg {width : Nat} [NeZero width] (reg : Nat) : HolProg width → Bool
  | .seq first second | .ite _ _ _ first second => keepsReg reg first && keepsReg reg second
  | .inst instruction => keepsInst reg instruction
  | .locValue dest _ _ => decide (dest ≠ reg)
  | .skip | .tick | .halt _ | .ret _ | .break _ | .continue _ => true
  | _ => false

theorem normalFrame {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (reg : Nat) (supported : keepsReg reg prog = true)
    (source post : StackSemStateFiniteExact width C F)
    (execution : evaluate (prog, source) = (none, post)) :
    post.regs.lookup reg = source.regs.lookup reg ∧ post.code = source.code := by
  cases prog with
  | seq first second =>
    have both : keepsReg reg first = true ∧ keepsReg reg second = true := by simpa [keepsReg] using supported
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at execution
    rcases run : evaluate (first, source) with ⟨result, middle⟩
    rw [run] at execution
    cases result with
    | none =>
      have a := normalFrame first reg both.1 source middle run
      have b := normalFrame second reg both.2 middle post execution
      exact ⟨b.1.trans a.1, b.2.trans a.2⟩
    | some result => simp at execution
  | ite cmp register operand first second =>
    have both : keepsReg reg first = true ∧ keepsReg reg second = true := by simpa [keepsReg] using supported
    rw [evaluate_ite] at execution
    repeat' split at execution
    all_goals first
      | exact normalFrame first reg both.1 source post execution
      | exact normalFrame second reg both.2 source post execution
      | simp_all
  | inst instruction =>
    rw [evaluate_inst] at execution
    cases run : StackSemInst.instHOL instruction source with
    | none => simp [run] at execution
    | some next =>
      simp only [run, Prod.mk.injEq, true_and] at execution
      subst next
      exact instFrame instruction reg supported source post run
  | skip =>
    have equal : source = post := by simpa [evaluate_skip] using execution
    subst post
    exact ⟨rfl, rfl⟩
  | tick =>
    rw [evaluate_tick] at execution
    split at execution
    · simp at execution
    · simp only [Prod.mk.injEq, true_and] at execution
      subst post
      exact ⟨rfl, rfl⟩
  | locValue dest label offset =>
    simp [keepsReg] at supported
    rw [evaluate_locValue] at execution
    split at execution
    · simp only [Prod.mk.injEq, true_and] at execution
      subst post
      simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, supported, Ne.symm supported]
    · simp at execution
  | halt register => rw [evaluate_halt] at execution; split at execution <;> simp_all
  | ret register => rw [evaluate_ret] at execution; split at execution <;> simp_all
  | «break» label => simp [evaluate_break] at execution
  | «continue» label => simp [evaluate_continue] at execution
  | _ => simp [keepsReg] at supported
termination_by sizeOf prog

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.normalFrame
