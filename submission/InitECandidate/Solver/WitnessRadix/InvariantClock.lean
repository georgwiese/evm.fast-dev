import InitECandidate.Solver.WitnessRadix.ConstructionInvariant

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- Clock changes preserve every memory, graph and task ownership invariant. -/
theorem invariant_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph) (clock : Nat) :
    Invariant { source with clock := clock } layout sliceFor expectedTree allocated completed depth context destination tasks graph := by
  let target := { source with clock := clock }
  refine ⟨inv.mapped, ?_, inv.atLayout, ?_, inv.rows, inv.present, inv.position, inv.length, inv.pendingValid,
    inv.parents, ?_, inv.pendingRows, inv.ordered, ?_, inv.located, ?_, inv.distinct, inv.aligned, inv.expected, inv.root, inv.budget⟩
  · exact immutable_of_agreement source target layout valid context.keyFor sliceFor rfl rfl (by intros; rfl) inv.immutable
  · exact SplitCount.task_locals_of_lookup source target context (by intros; rfl) inv.locals
  · exact PendingStack.represents_of_agreement source target rfl _ _ _ tasks (by intros; rfl) inv.stack
  · exact OpenGraph.represents_of_agreement source target rfl rfl layout.table layout.keys layout.vals graph (by intros; rfl) inv.represented
  · intro entry member read
    exact inv.safe entry member ((OpenGraph.reads_stable source target layout.table layout.keys layout.vals graph (by intros; rfl) entry.1).mpr read)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_clock
