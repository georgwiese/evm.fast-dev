import InitECandidate.Solver.Mpt.WitnessCoreRichDecode
import InitECandidate.Solver.Mpt.WitnessCoreRichResolve
import InitECandidate.Solver.Mpt.WitnessCoreRichReturn
import InitECandidate.Solver.Mpt.WitnessCoreLoopStep

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem RichInvariant.dec_clock (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (rich : RichInvariant input frontier db limit source cfg) : RichInvariant input frontier db limit (decClockHOLFinite source) cfg := by
  obtain ⟨registry⟩:=rich.registry
  obtain ⟨next,validEq⟩:=registry.of_fields source (decClockHOLFinite source) frontier db cfg rfl rfl rfl
  exact ⟨rich.base.dec_clock input frontier db limit source cfg,⟨next⟩⟩

/-- Every real continuing iteration of original238 moves to another
actual invariant state at strictly smaller physical rank. All three mode
transitions are derived from that iteration's genuine normal execution. -/
theorem RichInvariant.body_normal (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (rich : RichInvariant input frontier db limit source configuration) (frontierLower : 2713731432≤frontier) (running : configuration.running=true)
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) :
    ∃ next : Configuration,RichInvariant input frontier db limit post next ∧ next.rank limit<configuration.rank limit := by
  rcases configuration with ⟨heap,cursor,stack,phase,active⟩
  change active=true at running
  subst active
  rw [loop_body_choice source (modeWord phase) rich.base.modeCell] at normal
  cases phase with
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte] at normal
    exact rich.return_normal input frontier db heap cursor limit source post stack frontierLower normal
  | decode=>
    simp only [modeWord,if_pos rfl] at normal
    exact rich.decode_normal input frontier db heap cursor limit source post stack frontierLower normal
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte,if_pos rfl] at normal
    exact rich.resolve_normal input frontier db heap cursor limit source post stack frontierLower normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.dec_clock
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.body_normal
