import InitECandidate.Solver.WitnessRadix.LoopResult
import InitECandidate.Solver.WitnessRadix.InvariantFinishSupported

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def LoopSupported {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (expected : Graph.Tree) (weight : Nat) : Prop :=
  ∃ target : PanSemStateFiniteExact 64 F,∃ root : BitVec 64,
    evaluateHOLFiniteState source BuildEntry.mainLoop=(some (.returned (.val (.word 0#64))),target) ∧
    target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24)=.word root ∧
    QueryMemory.Represents target layout.table layout.keys layout.vals root expected ∧
    control target=control source ∧ source.clock-4*weight≤target.clock ∧ target.clock≤source.clock ∧
    (∀ query,QueryMemory.reads target layout.table layout.keys layout.vals root expected query → Protected layout layout.count query)

theorem result_next_supported {F : Type} (source next : PanSemStateFiniteExact 64 F) (layout : Layout) (expected : Graph.Tree)
    (weight nextWeight cost : Nat)
    (run : evaluateHOLFiniteState source BuildEntry.mainLoop=evaluateHOLFiniteState next BuildEntry.mainLoop)
    (fields : control next=control source) (clock : next.clock=source.clock-cost)
    (price : cost+4*nextWeight≤4*weight) (remaining : LoopSupported next layout expected nextWeight) :
    LoopSupported source layout expected weight := by
  obtain ⟨target,root,execution,mapped,word,represented,controls,lower,upper,support⟩:=remaining
  refine ⟨target,root,run.trans execution,mapped,word,represented,controls.trans fields,?_,?_,support⟩
  · rw [clock] at lower;omega
  · rw [clock] at upper;omega

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.result_next_supported
