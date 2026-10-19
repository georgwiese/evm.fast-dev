import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.CompareFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem not_equal_zero {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : ExpHOL 64) (lhs rhs : BitVec 64)
    (leftRead : eval source left=some (.val (.word lhs))) (rightRead : eval source right=some (.val (.word rhs)))
    (test : eval source (.cmp .notEqual left right)=some (.val (.word 0#64))) : lhs=rhs := by
  apply Classical.byContradiction
  intro different
  simp only [eval] at leftRead rightRead
  have one : eval source (.cmp .notEqual left right)=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,leftRead,rightRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different]
  have impossible : (1#64 : BitVec 64)=0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans test
  exact (by decide : (1#64 : BitVec 64)≠0#64) impossible

end InitECandidate.Solver.Input.CompareFacts

#print axioms InitECandidate.Solver.Input.CompareFacts.not_equal_zero
