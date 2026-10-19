import InitECandidate.Solver.Input.NoExceptionEvent
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actually raised literal guard exposes its exact identifier/payload
and readonly zero-clock effect, without assumed condition/shape success. -/
theorem literal_guard_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (actualIdentifier identifier : MlS) (word : BitVec 64) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.ite test (.raise actualIdentifier (.const word)) .skip) =
      (some (.exception identifier payload), post)) :
    identifier = actualIdentifier ∧ payload = .val (.word word) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite source ∧ post.clock = source.clock := by
  classical
  have idEq : identifier = actualIdentifier := by
    by_contra other
    have excluded := NoNamedException.conditional source.code identifier test _ _
      (NoNamedException.raised_other source.code identifier actualIdentifier (.const word) (Ne.symm other))
      (NoNamedException.of_all source.code identifier .skip (NoException.skip source.code))
    exact excluded source rfl payload (congrArg Prod.fst run)
  have payloadEq : payload = .val (.word word) := by
    by_contra other
    have excluded := NoExceptionEvent.conditional source.code identifier payload test _ _
      (NoExceptionEvent.raise_literal source.code identifier actualIdentifier payload word (Ne.symm other))
      (NoExceptionEvent.of_all source.code identifier payload .skip (NoException.skip source.code))
    exact excluded source rfl (congrArg Prod.fst run)
  have fields := LocalEffects.conditional source.code test _ _ (LocalEffects.raised source.code actualIdentifier (.const word)) (LocalEffects.skip source.code) source rfl
  have clock := QuietClock.conditional source.code test _ _ (QuietClock.raised source.code actualIdentifier (.const word)) (QuietClock.skip source.code) source rfl
  rw [run] at fields clock
  change LocalEffects.erase post = LocalEffects.erase source at fields
  change post.clock = source.clock at clock
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := post.clock}) fields
  change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := post.clock} at reset
  rw [clock] at reset
  exact ⟨idEq, payloadEq, reset, clock⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.literal_guard_exception
