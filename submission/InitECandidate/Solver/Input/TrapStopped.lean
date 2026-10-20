import InitECandidate.Solver.Input.TrapCost
import InitECandidate.Solver.Input.NoReturnIgnored

namespace InitECandidate.Solver.Input.Trap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual trap caller stops within one source tick, including errors,
timeouts, escaping exceptions and final FFI outcomes. No future success or
terminal oracle reply is assumed. -/
theorem stopped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values word)) :
    ∃ result target,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "trap_with") arguments) = (some result,target) ∧
      (∀ value,result ≠ .returned value) ∧ target.clock ≤ source.clock ∧ source.clock - target.clock ≤ 1 := by
  have cost := call_price source.code installed arguments source rfl
  have forward := evaluateHOLFiniteState_clock_le source (.call (some (none,none)) (ofString "trap_with") arguments)
  generalize outputEq : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "trap_with") arguments) = output at cost forward ⊢
  obtain ⟨result,target⟩ := output
  cases result with
  | none => exact False.elim (call_not_normal source target arguments word (original_code source.code installed) args outputEq)
  | some result =>
    refine ⟨result,target,rfl,?_,forward,cost⟩
    intro value bad
    have never := NoReturn.ignored_call (ofString "trap_with") arguments source value
    apply never
    rw [outputEq]
    exact congrArg some bad

end InitECandidate.Solver.Input.Trap

#print axioms InitECandidate.Solver.Input.Trap.stopped
