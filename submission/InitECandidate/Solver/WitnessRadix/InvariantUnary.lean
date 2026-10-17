import InitECandidate.Solver.WitnessRadix.InvariantClock
import InitECandidate.Solver.WitnessRadix.AgendaBudget
import InitECandidate.Solver.WitnessRadix.UnaryLoop

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open SplitScope

def unaryPost {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  QueryBranch.bind { source with clock := source.clock - context.input.length } "bit" (BitVec.ofNat 64 context.position + 1#64)

theorem unary_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (locals : SplitCount.TaskLocals source context) : SplitCount.TaskLocals (unaryPost source context) (unaryContext context) := by
  rcases locals with ⟨src, dst, keys, next, depth, start, count, bit, dest, pendingStart, pendingCount, pendingNode⟩
  simp [ofString] at src dst keys next depth start count dest pendingStart pendingCount pendingNode
  constructor
  all_goals simp [unaryPost, unaryContext, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
    FUPDATE, ofString, src, dst, keys, next, depth, start, count, dest, pendingStart, pendingCount, pendingNode, BitVec.ofNat_add]

theorem unary_layout (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) : ContextAt layout (unaryContext context) allocated depth destination := by
  rcases atLayout with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩

theorem unary_aligned (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (aligned : Aligned context sliceFor tasks graph) (inside : context.position < 256)
    (uniform : zeroCount context = 0 ∨ zeroCount context = context.input.length) :
    Aligned (unaryContext context) sliceFor tasks graph := by
  change OpenGraph.frontier graph = (context.dest, OrdinalTree.tree context.keyFor sliceFor (context.position + 1) context.input) :: _
  rw [← OrdinalTree.unary context.keyFor sliceFor context.position context.input inside uniform]
  exact aligned

/-- Complete actual unary body, including counting and temporary restoration,
retains the full invariant while advancing the shared key bit. -/
theorem invariant_unary {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph)
    (inside : context.position < 256) (many : 1 < context.input.length)
    (uniform : zeroCount context = 0 ∨ zeroCount context = context.input.length) (enough : context.input.length ≤ source.clock) :
    evaluateHOLFiniteState source BuildEntry.mainBody = (some .continue, unaryPost source context) ∧
      Invariant (unaryPost source context) layout sliceFor expectedTree allocated completed depth
        (unaryContext context) destination tasks graph := by
  let target := unaryPost source context
  have small : context.input.length < 2 ^ 64 := by
    have countBound := count_small layout valid
    have fits := inv.atLayout.interval
    omega
  have ready := context_ready source layout context allocated depth destination inv.atLayout valid inv.mapped sliceFor inv.immutable inv.rows
  have execution := UnaryProgram.main_body_unary source context.src (BitVec.ofNat 64 context.start) context.keys context.keyFor
    context.input context.position inside small many inv.locals.srcLocal inv.locals.startLocal inv.locals.keysLocal inv.locals.bitLocal
    inv.locals.countLocal inv.rows ready.views uniform enough
  refine ⟨execution, ?_⟩
  refine ⟨inv.mapped,
    immutable_of_agreement source target layout valid context.keyFor sliceFor rfl rfl (by intros; rfl) inv.immutable,
    unary_layout layout context allocated depth destination inv.atLayout, unary_locals source context inv.locals,
    inv.rows, inv.present, (by change context.position + 1 ≤ 256; omega), inv.length, inv.pendingValid, inv.parents,
    PendingStack.represents_of_agreement source target rfl _ _ _ tasks (by intros; rfl) inv.stack,
    inv.pendingRows, inv.ordered,
    OpenGraph.represents_of_agreement source target rfl rfl layout.table layout.keys layout.vals graph (by intros; rfl) inv.represented,
    inv.located, ?_, inv.distinct, unary_aligned context sliceFor tasks graph inv.aligned inside uniform, inv.expected, inv.root,
    unary_agenda_budget layout context tasks completed allocated inv.budget⟩
  intro entry member read
  exact inv.safe entry member ((OpenGraph.reads_stable source target layout.table layout.keys layout.vals graph (by intros; rfl) entry.1).mpr read)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_unary
