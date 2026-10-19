import InitECandidate.Solver.Rlp.FailGuard

namespace InitECandidate.Solver.Rlp.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem lower_guard (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64)
    (lhs rhs : BitVec 64) (arguments : List (ExpHOL 64))
    (leftRead : eval source left=some (.val (.word lhs))) (rightRead : eval source right=some (.val (.word rhs)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.ite (.cmp .lower left right) (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "rlp_fail") arguments) .skip)=(none,post)) :
    rhs.toNat≤lhs.toNat ∧ post=source := by
  classical
  obtain ⟨passed,same⟩ := guard_normal source post (.cmp .lower left right) arguments installed normal
  refine ⟨?_,same⟩
  by_contra excessive
  have lt : lhs.toNat<rhs.toNat := by omega
  simp only [eval] at leftRead rightRead
  have one : eval source (.cmp .lower left right)=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,leftRead,rightRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,lt]
  have impossible : (1#64 : BitVec 64)=0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
  exact (by decide : (1#64 : BitVec 64)≠0#64) impossible

theorem equal_guard (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64)
    (lhs rhs : BitVec 64) (arguments : List (ExpHOL 64))
    (leftRead : eval source left=some (.val (.word lhs))) (rightRead : eval source right=some (.val (.word rhs)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.ite (.cmp .equal left right) (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "rlp_fail") arguments) .skip)=(none,post)) :
    lhs≠rhs ∧ post=source := by
  classical
  obtain ⟨passed,same⟩ := guard_normal source post (.cmp .equal left right) arguments installed normal
  refine ⟨?_,same⟩
  intro equal
  simp only [eval] at leftRead rightRead
  have one : eval source (.cmp .equal left right)=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,leftRead,rightRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,equal]
  have impossible : (1#64 : BitVec 64)=0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
  exact (by decide : (1#64 : BitVec 64)≠0#64) impossible

end InitECandidate.Solver.Rlp.Fail

#print axioms InitECandidate.Solver.Rlp.Fail.lower_guard
#print axioms InitECandidate.Solver.Rlp.Fail.equal_guard
