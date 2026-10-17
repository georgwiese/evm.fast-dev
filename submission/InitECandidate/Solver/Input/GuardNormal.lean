import InitECandidate.Solver.Input.HeaderGuards

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal continuation through the actual decoder guard rules out its
error predicate. Rejection performs the real ssz_fail and cannot resume. -/
theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64)
    (error : BitVec 64) (bad : Prop) [Decidable bad]
    (test : eval source condition=some (.val (.word (if bad then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq (.ite condition (.call (some (none,none)) (ofString "ssz_fail") [.const error]) .skip) continuation)=
      (some (.returned value),post)) :
    ¬bad ∧ evaluateHOLFiniteState source continuation=(some (.returned value),post) := by
  have guarded:=Header.test_guard_execute source condition error bad test code exceptionShape enough
  by_cases rejected : bad
  · simp only [if_pos rejected] at guarded
    have stopped:=WitnessRadix.StateSteps.stopped_sequence source _ _ continuation (.exception (ofString "SszErr") (.val (.word error)))
      guarded (by change source.clock-1≤source.clock; omega)
    rw [stopped] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · simp only [if_neg rejected] at guarded
    exact ⟨rejected,(WitnessRadix.StateSteps.next_sequence source source _ continuation guarded (Nat.le_refl _)).symm.trans run⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.guard_normal
