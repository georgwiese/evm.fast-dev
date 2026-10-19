import InitECandidate.Solver.Rlp.NumericGuards
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Rlp.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Invert a real enclosing return through a failure guard. The original
guard passed without changing state, then the actual suffix returned. -/
theorem guard_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip) continuation)=(some (.returned returned),post)) :
    evaluateHOLFiniteState source (.ite test (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip)=(none,source) ∧
      evaluateHOLFiniteState source continuation=(some (.returned returned),post) := by
  have safe : Input.LocalPrefix (ofString "p") (.ite test (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip) :=
    .ite test (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,firstRun,tailRun,locals⟩ := safe.normal_continue source post continuation returned normal
  have same := (guard_normal source middle test arguments installed firstRun).2
  subst middle
  exact ⟨firstRun,tailRun⟩

theorem lower_guard_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64)
    (lhs rhs : BitVec 64) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (leftRead : WitnessRadix.QueryBranch.eval source left=some (.val (.word lhs)))
    (rightRead : WitnessRadix.QueryBranch.eval source right=some (.val (.word rhs)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq (.ite (.cmp .lower left right) (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip) continuation)=(some (.returned returned),post)) :
    rhs.toNat≤lhs.toNat ∧ evaluateHOLFiniteState source continuation=(some (.returned returned),post) := by
  obtain ⟨front,tailRun⟩ := guard_return source post (.cmp .lower left right) arguments continuation returned installed normal
  exact ⟨(lower_guard source source left right lhs rhs arguments leftRead rightRead installed front).1,tailRun⟩

theorem equal_guard_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64)
    (lhs rhs : BitVec 64) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (leftRead : WitnessRadix.QueryBranch.eval source left=some (.val (.word lhs)))
    (rightRead : WitnessRadix.QueryBranch.eval source right=some (.val (.word rhs)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq (.ite (.cmp .equal left right) (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip) continuation)=(some (.returned returned),post)) :
    lhs≠rhs ∧ evaluateHOLFiniteState source continuation=(some (.returned returned),post) := by
  obtain ⟨front,tailRun⟩ := guard_return source post (.cmp .equal left right) arguments continuation returned installed normal
  exact ⟨(equal_guard source source left right lhs rhs arguments leftRead rightRead installed front).1,tailRun⟩

end InitECandidate.Solver.Rlp.Fail

#print axioms InitECandidate.Solver.Rlp.Fail.guard_return
#print axioms InitECandidate.Solver.Rlp.Fail.lower_guard_return
#print axioms InitECandidate.Solver.Rlp.Fail.equal_guard_return
