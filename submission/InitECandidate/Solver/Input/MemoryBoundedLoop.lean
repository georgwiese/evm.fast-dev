import InitECandidate.Solver.Input.MemoryNormal
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Protected memory through an actual normal bounded counter/stride loop.
The supplied current-state test law and normal-body transition derive every
in-range iteration. This is a frame, not a termination or runtime premise. -/
theorem bounded_counter_loop_normal (code) (counter marker : MlS) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat) (query : BitVec 64)
    (safe : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary marker body current)
    (advance : CounterFlow.Advances counter stride body)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory→Prop)
    (decClock : ∀ current,invariant current → invariant (decClockHOLFinite current))
    (readTest : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,invariant current → ∀ index : Nat,index≤length →
      current.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index))) →
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word (if index+stride≤length then 1#64 else 0#64))))
    (stepFrame : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → invariant current → ∀ index : Nat,index+stride≤length →
      current.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index))) → ∀ target,
      evaluateHOLFiniteState current body=(none,target) → invariant target ∧ target.memory query=current.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (initial : Nat)
    (codeEq : source.code=code) (ready : invariant source) (inside : initial≤length)
    (position : source.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 initial))))
    (run : evaluateHOLFiniteState source (.while test body)=(none,post)) :
    invariant post ∧ (∃ index : Nat,index≤length ∧ post.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index)))) ∧ post.memory query=source.memory query := by
  let valid := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>invariant current ∧
    (∃ index : Nat,index≤length ∧ current.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index)))) ∧ current.memory query=source.memory query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → valid current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target) → valid target := by
    intro current installed actual word read nonzero funded target bodyRun
    obtain ⟨currentReady,⟨index,indexBound,indexCell⟩,memory⟩ := actual
    have expected := readTest current currentReady index indexBound indexCell
    have active : index+stride≤length := by
      by_cases active : index+stride≤length
      · exact active
      rw [if_neg active] at expected
      have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact False.elim (nonzero zero)
    have next := stepFrame (decClockHOLFinite current) installed (decClock current currentReady) index active indexCell target bodyRun
    have nextCell : target.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 (index+stride)))) := by
      simpa only [BitVec.ofNat_add] using advance (decClockHOLFinite current) target (BitVec.ofNat 64 index) indexCell bodyRun
    exact ⟨next.1,⟨index+stride,active,nextCell⟩,next.2.trans memory⟩
  exact loop_invariant_summary code marker test body safe valid transition source post codeEq ⟨ready,⟨initial,inside,position⟩,rfl⟩ run

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.bounded_counter_loop_normal
