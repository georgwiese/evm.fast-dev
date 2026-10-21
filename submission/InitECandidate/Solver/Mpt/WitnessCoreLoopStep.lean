import InitECandidate.Solver.Mpt.WitnessCoreLoopDecode
import InitECandidate.Solver.Mpt.WitnessCoreLoopResolve
import InitECandidate.Solver.Mpt.WitnessCoreLoopReturn
import InitECandidate.Solver.Mpt.WitnessCoreLoopControl

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem Invariant.condition (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant input frontier db limit source configuration) :
    eval source WitnessCore.condition=some (.val (.word (goWord configuration.running))) := by
  have go:=invariant.goCell
  cases running : configuration.running <;>
    simp [eval,WitnessCore.condition,evalHOLExact,localVar,toExact,go,goWord,running,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Every real continuing iteration of original238 moves to another
actual invariant state at strictly smaller physical rank. All three mode
transitions are derived from that iteration's genuine normal execution. -/
theorem Invariant.body_normal (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant input frontier db limit source configuration) (running : configuration.running=true)
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) :
    ∃ next : Configuration,Invariant input frontier db limit post next ∧ next.rank limit<configuration.rank limit := by
  rcases configuration with ⟨heap,cursor,stack,phase,active⟩
  change active=true at running
  subst active
  rw [loop_body_choice source (modeWord phase) invariant.modeCell] at normal
  cases phase with
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte] at normal
    exact invariant.return_normal input frontier db heap cursor limit source post stack normal
  | decode=>
    simp only [modeWord,if_pos rfl] at normal
    exact invariant.decode_normal input frontier db heap cursor limit source post stack normal
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte,if_pos rfl] at normal
    exact invariant.resolve_normal input frontier db heap cursor limit source post stack normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.condition
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.body_normal
