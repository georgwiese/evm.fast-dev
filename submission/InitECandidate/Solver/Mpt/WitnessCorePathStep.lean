import InitECandidate.Solver.Mpt.WitnessCorePathDecode
import InitECandidate.Solver.Mpt.WitnessCorePathResolve
import InitECandidate.Solver.Mpt.WitnessCorePathReturn
import InitECandidate.Solver.Mpt.WitnessCoreLoopStep

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every real continuing iteration of original238 moves to another
actual invariant state at strictly smaller physical rank. All three mode
transitions are derived from that iteration's genuine normal execution. -/
theorem PathInvariant.body_normal (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (model : PathInvariant input frontier db limit source configuration) (frontierLower : 2713731432≤frontier) (running : configuration.running=true)
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) :
    ∃ next : Configuration,PathInvariant input frontier db limit post next ∧ next.rank limit<configuration.rank limit := by
  rcases configuration with ⟨heap,cursor,stack,phase,active⟩
  change active=true at running
  subst active
  rw [loop_body_choice source (modeWord phase) model.base.modeCell] at normal
  cases phase with
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte] at normal
    exact model.return_normal input frontier db heap cursor limit source post stack frontierLower normal
  | decode=>
    simp only [modeWord] at normal
    exact model.decode_normal input frontier db heap cursor limit source post stack frontierLower normal
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte] at normal
    exact model.resolve_normal input frontier db heap cursor limit source post stack frontierLower normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.body_normal
