import InitECandidate.Solver.Input.MemoryNormal
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A normal fixed-size original counter loop retains a protected word and
its current invariant. Per-step facts apply only to actual in-range counters
and actual normal bodies; no later successful execution is an assumption. -/
theorem constant_loop_normal (code) (counter marker : MlS) (body : ProgHOL 64) (length : Nat) (query : BitVec 64)
    (small : length<9223372036854775808)
    (safe : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary marker body current)
    (advance : CounterFlow.Advances counter 1 body)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory→Prop)
    (decClock : ∀ current,invariant current → invariant (decClockHOLFinite current))
    (stepFrame : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → invariant current → ∀ index : Nat,index<length →
      current.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index))) → ∀ target,
      evaluateHOLFiniteState current body=(none,target) → invariant target ∧ target.memory query=current.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (initial : Nat)
    (codeEq : source.code=code) (ready : invariant source) (inside : initial≤length)
    (position : source.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 initial))))
    (run : evaluateHOLFiniteState source (.while (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length))) body)=(none,post)) :
    invariant post ∧ (∃ index : Nat,index≤length ∧ post.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index)))) ∧ post.memory query=source.memory query := by
  let valid := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>invariant current ∧
    (∃ index : Nat,index≤length ∧ current.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 index)))) ∧ current.memory query=source.memory query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → valid current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target) → valid target := by
    intro current installed actual word read nonzero funded target bodyRun
    obtain ⟨currentReady,⟨index,indexBound,indexCell⟩,memory⟩ := actual
    have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have lengthNumber : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have expected : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) (.cmp .less (.var .local counter) (.const (BitVec.ofNat 64 length)))=
        some (.val (.word (if index<length then 1#64 else 0#64))) := by
      simp [evalHOLFinite,evalHOLExact,toExact,indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
        iNumber,lengthNumber,show index<9223372036854775808 from by omega,small]
    have active : index<length := by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    have next := stepFrame (decClockHOLFinite current) installed (decClock current currentReady) index active indexCell target bodyRun
    have nextCell : target.locals.lookup counter=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
      simpa only [BitVec.ofNat_add] using advance (decClockHOLFinite current) target (BitVec.ofNat 64 index) indexCell bodyRun
    exact ⟨next.1,⟨index+1,by omega,nextCell⟩,next.2.trans memory⟩
  exact loop_invariant_summary code marker _ body safe valid transition source post codeEq ⟨ready,⟨initial,inside,position⟩,rfl⟩ run

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.constant_loop_normal
