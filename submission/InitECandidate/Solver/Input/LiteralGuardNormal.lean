import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- Actual normal continuation through a direct literal-raise guard proves
that its error predicate is false. Invalid exception metadata still cannot
fall through; no assumption about a future successful guard is supplied. -/
theorem literal_guard_normal {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (test : ExpHOL 64) (identifier : MlS) (error : BitVec 64) (bad : Prop) [Decidable bad]
    (read : eval source test=some (.val (.word (if bad then 1#64 else 0#64))))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (.raise identifier (.const error)) .skip) continuation)=(some (.returned value),post)) :
    ¬bad ∧ evaluateHOLFiniteState source continuation=(some (.returned value),post) := by
  have guard : PureGuard (.ite test (.raise identifier (.const error)) .skip) := .ite test (.raise _ _) .skip
  have passed := guard.normal_passed source post continuation value normal
  refine ⟨?_,guard.normal_continue source post continuation value normal⟩
  intro rejected
  have branch : evaluateHOLFiniteState source (.ite test (.raise identifier (.const error)) .skip)=
      evaluateHOLFiniteState source (.raise identifier (.const error)) := by
    change @evalHOLExact 64 F _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) test=_ at read
    rw [evaluateHOLFiniteState_ite,read,if_pos rejected]
    simp
  rw [branch] at passed
  exact raise_ne_none source identifier (.const error) (congrArg Prod.fst passed)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.literal_guard_normal
