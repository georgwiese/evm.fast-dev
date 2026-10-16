import InitECandidate.Solver.FlattenWeighted.BlockBound

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate InitECandidate.Solver.FlattenBound

/-- Right-associated sequencing, matching the fixed compiler's actual DAG. -/
def prefixChain {width : Nat} [NeZero width] (blocks : List (HolProg width)) (tail : HolProg width) : HolProg width :=
  blocks.foldr .seq tail

def prefixCredits {width : Nat} [NeZero width] (blocks : List (HolProg width)) : Nat :=
  (blocks.map (fun prog => ticks prog + nodes prog)).sum

def prefixClocks {width : Nat} [NeZero width] (blocks : List (HolProg width)) : Nat :=
  (blocks.map ticks).sum

private theorem seqEvaluate {width : Nat} [NeZero width] {C F : Type}
    (p q : HolProg width) (state : StackSemStateFiniteExact width C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- A basic prefix pays only for its constituent blocks and supplies a normal
state transition to the bounded tail. Failed prefixes stop before the tail. -/
theorem BlockBound.basicPrefix {width : Nat} [NeZero width] {C F : Type}
    (blocks : List (HolProg width)) (tail : HolProg width)
    (pre middle post : StackSemStateFiniteExact width C F → Prop)
    (credits clocks : Nat)
    (supported : ∀ prog ∈ blocks, FlattenWeighted.basic prog = true)
    (transfer : ∀ source next, pre source → evaluate (prefixChain blocks .skip, source) = (none, next) → middle next)
    (bound : BlockBound tail middle post credits clocks) :
    BlockBound (prefixChain blocks tail) pre post (prefixCredits blocks + credits) (prefixClocks blocks + clocks) := by
  induction blocks generalizing pre with
  | nil =>
    apply bound.weaken ?_ (fun _ h => h) (by simp [prefixCredits]) (by simp [prefixClocks])
    intro state valid
    exact transfer state state valid (by simp [prefixChain, evaluate_skip])
  | cons first rest ih =>
    let afterFirst := fun next => ∃ source, pre source ∧ evaluate (first, source) = (none, next)
    have firstBound : BlockBound first pre afterFirst (ticks first + nodes first) (ticks first) :=
      BlockBound.basic first pre afterFirst (supported first (by simp))
        (fun source next valid run => ⟨source, valid, run⟩)
    have restBound := ih afterFirst (fun prog member => supported prog (by simp [member])) (by
      intro state next valid run
      obtain ⟨source, initial, firstRun⟩ := valid
      apply transfer source next initial
      change evaluate (.seq first (prefixChain rest .skip), source) = _
      rw [seqEvaluate, firstRun]
      exact run)
    have combined := firstBound.seq restBound
    apply combined.weaken (fun _ h => h) (fun _ h => h) <;>
      simp [prefixCredits, prefixClocks] <;> omega

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.basicPrefix
