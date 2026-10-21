import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A genuine enclosing return passes the actual MPT failure guard at
unchanged state, then returns through its real suffix. -/
theorem guard_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (.call (some (none,none)) (ofString "mpt_fail") arguments) .skip) continuation)=(some (.returned returned),post)) :
    evaluateHOLFiniteState source (.ite test (.call (some (none,none)) (ofString "mpt_fail") arguments) .skip)=(none,source) ∧
      evaluateHOLFiniteState source continuation=(some (.returned returned),post) := by
  have safe : Input.LocalPrefix (ofString "p") (.ite test (.call (some (none,none)) (ofString "mpt_fail") arguments) .skip):=
    .ite test (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,firstRun,tailRun,locals⟩:=safe.normal_continue source post continuation returned normal
  have same:=(guard_normal source middle test arguments installed firstRun).2
  subst middle
  exact ⟨firstRun,tailRun⟩

end InitECandidate.Solver.Mpt.Fail

#print axioms InitECandidate.Solver.Mpt.Fail.guard_return
