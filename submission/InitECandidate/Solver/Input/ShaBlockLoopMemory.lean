import InitECandidate.Solver.Input.ShaBlockStepMemory
import InitECandidate.Solver.Input.MemoryConstantLoop
import InitECandidate.Solver.Input.GlobalEffectsAtoms

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive LoopPhase where | pack | unpack

def LoopPhase.program : LoopPhase→ProgHOL 64 | .pack=>firstStep | .unpack=>secondStep

theorem LoopPhase.other (phase : LoopPhase) (key : MlS) (differentI : key≠ofString "i")
    (differentLo : key≠ofString "lo") (differentHi : key≠ofString "hi") (differentPacked : key≠ofString "packed") : LocalPrefix key phase.program := by
  cases phase
  · rw [LoopPhase.program,first_memory_shape]
    exact .dec _ _ _ differentLo (.dec _ _ _ differentHi (.seq (.store _ _) (.assign _ _ differentI)))
  · rw [LoopPhase.program,second_memory_shape]
    exact .dec _ _ _ differentPacked (.seq (.store _ _) (.seq (.store _ _) (.assign _ _ differentI)))

theorem LoopPhase.advance (phase : LoopPhase) : CounterFlow.Advances (ofString "i") 1 phase.program := by
  cases phase
  · rw [LoopPhase.program,first_memory_shape]
    apply CounterFlow.declared (other:=by decide)
    apply CounterFlow.declared (other:=by decide)
    exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.store _ _)) (CounterFlow.increment _)
  · rw [LoopPhase.program,second_memory_shape]
    apply CounterFlow.declared (other:=by decide)
    apply CounterFlow.sequence (left:=0) (right:=1)
    · exact CounterFlow.preserved _ _ (.store _ _)
    · exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.store _ _)) (CounterFlow.increment _)

theorem LoopPhase.globals (phase : LoopPhase) (key : MlS) (code) : GlobalEffects.Preserves key code phase.program := by
  cases phase <;> simp only [LoopPhase.program,first_memory_shape,second_memory_shape,firstMemoryTail,secondMemoryTail,increment]
  all_goals repeat' first | apply GlobalEffects.declared | apply GlobalEffects.sequence | exact GlobalEffects.store key code _ _ | exact GlobalEffects.assign key code _ _

structure BlockMemoryReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel : BitVec 64) : Prop where
  state : source.locals.lookup (ofString "stp")=some (.val (.word pointer))
  accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel))

theorem LoopPhase.after (phase : LoopPhase) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel : BitVec 64)
    (ready : BlockMemoryReady source pointer accel) (run : evaluateHOLFiniteState source phase.program=(none,post)) : BlockMemoryReady post pointer accel := by
  have localFrame := (phase.other (ofString "stp") (by decide) (by decide) (by decide) (by decide)).summary_full source
  unfold LocalSummary at localFrame
  rw [run] at localFrame
  have globalFrame := phase.globals (ofString "sha_accel") source.code source rfl
  rw [run] at globalFrame
  exact ⟨(localFrame.1 rfl).trans ready.state,(congrArg Prod.snd globalFrame).trans ready.accelerator⟩

/-- Each genuine normal pack/unpack loop retains its pointer facts and
bounded real counter, and preserves words outside the two real buffers. -/
theorem LoopPhase.memory (phase : LoopPhase) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel)
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (run : evaluateHOLFiniteState source (.while (.cmp .less (localVar "i") (.const 4#64)) phase.program)=(none,post)) :
    BlockMemoryReady post pointer accel ∧ (∃ index : Nat,index≤4 ∧ post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) ∧ post.memory query=source.memory query := by
  exact MemoryAt.constant_loop_normal source.code (ofString "i") (ofString "marker") phase.program 4 query (by decide)
    (phase.other (ofString "marker") (by decide) (by decide) (by decide) (by decide)).summary_full phase.advance
    (fun current=>BlockMemoryReady current pointer accel) (by intro current actual; exact ⟨actual.state,actual.accelerator⟩)
    (by intro current installed actual index active currentPosition target bodyRun
        refine ⟨phase.after current target pointer accel actual bodyRun,?_⟩
        cases phase
        · exact first_step_memory current target accel query index active actual.accelerator currentPosition accelAway bodyRun
        · exact second_step_memory current target pointer query index active actual.state currentPosition stateAway bodyRun)
    source post 0 rfl ready (by decide) position run

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.LoopPhase.other
#print axioms InitECandidate.Solver.Input.ShaFixedCost.LoopPhase.advance
#print axioms InitECandidate.Solver.Input.ShaFixedCost.LoopPhase.globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.LoopPhase.after
#print axioms InitECandidate.Solver.Input.ShaFixedCost.LoopPhase.memory
