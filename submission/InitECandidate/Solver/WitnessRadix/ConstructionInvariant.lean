import InitECandidate.Solver.WitnessRadix.FrontierAlignment
import InitECandidate.Solver.WitnessRadix.LayoutPendingRows
import InitECandidate.Solver.WitnessRadix.FrontierBudget

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

def activeAgendaTask (context : SplitContext) : WitnessRadix.Task (BitVec 64) Unit :=
  ⟨context.position, 256 - context.position, context.input.map fun ordinal => (ordinal, ())⟩
def savedAgendaTask (task : PendingStack.Task) : WitnessRadix.Task (BitVec 64) Unit :=
  ⟨task.parentPosition + 1, 256 - (task.parentPosition + 1), task.input.map fun ordinal => (ordinal, ())⟩
def agenda (context : SplitContext) (tasks : List PendingStack.Task) : List (WitnessRadix.Task (BitVec 64) Unit) :=
  activeAgendaTask context :: tasks.map savedAgendaTask

/-- Memory, task and graph invariants for the actual outer construction loop.
Clock affordability is kept in the loop theorem so each while payment is explicit. -/
structure Invariant {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree) : Prop where
  mapped : Mapped source layout
  immutable : Immutable source layout context.keyFor sliceFor
  atLayout : ContextAt layout context allocated depth destination
  locals : SplitCount.TaskLocals source context
  rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input
  present : context.input ≠ []
  position : context.position ≤ 256
  length : tasks.length = depth
  pendingValid : ValidPending layout tasks
  parents : ParentsWithin layout allocated tasks
  stack : PendingStack.Represents source context.pendingStart context.pendingCount context.pendingNode tasks
  pendingRows : PendingRows source layout tasks
  ordered : PendingStack.OrderedFrom (context.start + context.input.length) tasks
  represented : OpenGraph.Represents source layout.table layout.keys layout.vals graph
  located : Located layout allocated graph
  safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals graph
  distinct : ((OpenGraph.frontier graph).map Prod.fst).Nodup
  aligned : Aligned context sliceFor tasks graph
  expected : OpenGraph.expected graph = expectedTree
  root : OpenGraph.slot graph = cell layout .header 24
  budget : FrontierBudget layout.count completed allocated (agenda context tasks)

theorem invariant_branch_room {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph) :
    allocated < layout.count := frontier_branch_room inv.budget

theorem invariant_stack_room {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph) :
    depth < layout.count := by
  have slots := agenda_length_le_records (agenda context tasks) inv.budget.valid
  have mass := inv.budget.mass
  dsimp only [agenda] at mass
  simp only [agenda, List.length_cons, List.length_map] at slots
  have length := inv.length
  omega

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_branch_room
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_stack_room
