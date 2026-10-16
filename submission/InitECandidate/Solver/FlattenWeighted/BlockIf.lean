import InitECandidate.Solver.FlattenWeighted.BlockBound

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm StackSemEvaluate

theorem BlockBound.ite {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (register : Nat) (operand : HolRegImm width)
    {first second : HolProg width} {pre post : StackSemStateFiniteExact width C F → Prop}
    {credits clocks : Nat}
    (left : BlockBound first pre post credits clocks)
    (right : BlockBound second pre post credits clocks) :
    BlockBound (.ite cmp register operand first second) pre post (credits + 1) clocks := by
  constructor
  · intro state valid
    exact Work.ite (fun _ => left.work state valid) (fun _ => right.work state valid)
  · intro state valid
    have firstClock := left.clock state valid
    have secondClock := right.clock state valid
    rw [evaluate_ite]
    repeat' split
    all_goals (try dsimp only)
    all_goals omega
  · intro state next valid run
    have firstNormal := left.normal state next valid
    have secondNormal := right.normal state next valid
    rw [evaluate_ite] at run
    repeat' split at run
    all_goals first | exact firstNormal run | exact secondNormal run | simp at run
  · intro state next valid run
    have firstTimeout := left.timeout state next valid
    have secondTimeout := right.timeout state next valid
    rw [evaluate_ite] at run
    repeat' split at run
    all_goals first | exact firstTimeout run | exact secondTimeout run | simp at run

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.ite
