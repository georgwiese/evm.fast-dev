import InitECandidate.Solver.FlattenWeighted.BasicTimeout
import InitECandidate.Solver.FlattenWeighted.Work

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Solver.FlattenBound

/-- A composable bound for an actual source block. The normal postcondition
is required only when control reaches the next block. Timeout leaves zero
clock, permitting a sufficient initial clock to be chosen after composition. -/
structure BlockBound {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (pre post : StackSemStateFiniteExact width C F → Prop)
    (credits clocks : Nat) : Prop where
  work : ∀ state, pre state → Work prog state credits
  clock : ∀ state, pre state → state.clock ≤ (evaluate (prog, state)).2.clock + clocks
  normal : ∀ state next, pre state → evaluate (prog, state) = (none, next) → post next
  timeout : ∀ state next, pre state → evaluate (prog, state) = (some .timeOut, next) → next.clock = 0

private theorem seqEvaluate {width : Nat} [NeZero width] {C F : Type}
    (p q : HolProg width) (state : StackSemStateFiniteExact width C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

theorem BlockBound.seq {width : Nat} [NeZero width] {C F : Type}
    {first second : HolProg width} {pre middle post : StackSemStateFiniteExact width C F → Prop}
    {firstCredits secondCredits firstClocks secondClocks : Nat}
    (left : BlockBound first pre middle firstCredits firstClocks)
    (right : BlockBound second middle post secondCredits secondClocks) :
    BlockBound (.seq first second) pre post (firstCredits + secondCredits) (firstClocks + secondClocks) := by
  constructor
  · intro state valid
    apply Work.seq (left.work state valid)
    intro next run
    exact right.work next (left.normal state next valid run)
  · intro state valid
    have firstClock := left.clock state valid
    rw [seqEvaluate]
    rcases run : evaluate (first, state) with ⟨result, next⟩
    rw [run] at firstClock
    cases result with
    | none =>
      have secondClock := right.clock next (left.normal state next valid run)
      dsimp only at firstClock ⊢
      omega
    | some result =>
      dsimp only at firstClock ⊢
      omega
  · intro state next valid run
    rw [seqEvaluate] at run
    rcases firstRun : evaluate (first, state) with ⟨result, intermediate⟩
    rw [firstRun] at run
    cases result with
    | none => exact right.normal intermediate next (left.normal state intermediate valid firstRun) run
    | some result => simp at run
  · intro state next valid run
    rw [seqEvaluate] at run
    rcases firstRun : evaluate (first, state) with ⟨result, intermediate⟩
    rw [firstRun] at run
    cases result with
    | none => exact right.timeout intermediate next (left.normal state intermediate valid firstRun) run
    | some result =>
      have sameResult : some result = some .timeOut := congrArg Prod.fst run
      have sameState : intermediate = next := congrArg Prod.snd run
      rw [sameResult, sameState] at firstRun
      exact left.timeout state next valid firstRun

theorem BlockBound.basic {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (pre post : StackSemStateFiniteExact width C F → Prop)
    (supported : basic prog = true)
    (normal : ∀ state next, pre state → evaluate (prog, state) = (none, next) → post next) :
    BlockBound prog pre post (ticks prog + nodes prog) (ticks prog) where
  work := fun _ _ => Work.basic supported
  clock := fun state _ => basicClock prog state supported
  normal := normal
  timeout := by
    intro state next _ run
    have zero := basicTimeoutClock prog state supported
    rw [run] at zero
    exact zero rfl

theorem BlockBound.weaken {width : Nat} [NeZero width] {C F : Type}
    {prog : HolProg width} {pre post pre' post' : StackSemStateFiniteExact width C F → Prop}
    {credits clocks credits' clocks' : Nat} (bound : BlockBound prog pre post credits clocks)
    (before : ∀ state, pre' state → pre state) (after : ∀ state, post state → post' state)
    (workLe : credits ≤ credits') (clockLe : clocks ≤ clocks') :
    BlockBound prog pre' post' credits' clocks' where
  work := fun state valid => Work.mono workLe (bound.work state (before state valid))
  clock := by
    intro state valid
    have enough := bound.clock state (before state valid)
    omega
  normal := fun state next valid run => after next (bound.normal state next (before state valid) run)
  timeout := fun state next valid run => bound.timeout state next (before state valid) run

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.seq
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.basic
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.weaken
