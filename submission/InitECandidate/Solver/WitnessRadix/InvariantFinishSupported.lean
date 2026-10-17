import InitECandidate.Solver.WitnessRadix.OpenGraphCompletedSupport
import InitECandidate.Solver.WitnessRadix.InvariantTerminal
import InitECandidate.Solver.WitnessRadix.LayoutTerminalFinish

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- With no pending task, the actual final body returns and establishes the
complete lookup representation at the original table's root header cell. -/
theorem invariant_terminal_finish_supported {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination [] graph)
    (stop : context.input.length = 1 ∨ context.position = 256) (ordinal : BitVec 64) (last : context.input.getLast? = some ordinal) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
      evaluateHOLFiniteState source BuildEntry.mainBody = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (OpenGraph.leafPost source context.dest ordinal.toNat) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root expectedTree ∧
      (∀ query,QueryMemory.reads target layout.table layout.keys layout.vals root expectedTree query →
        Protected layout layout.count query) := by
  have depthZero : depth = 0 := by have length := inv.length; simp only [List.length_nil] at length; omega
  subst depth
  have branchRoom := invariant_branch_room source layout sliceFor expectedTree allocated completed 0 context destination [] graph inv
  have ordinalBound := inv.atLayout.ordinals ordinal (List.mem_of_getLast? last)
  have treeEq : currentTree context sliceFor =
      .leaf (context.keyFor (BitVec.ofNat 64 ordinal.toNat)) (sliceFor (BitVec.ofNat 64 ordinal.toNat)) := by
    have model := OrdinalTree.terminal context.keyFor sliceFor context.position context.input ordinal last stop.symm
    simpa [currentTree] using model
  obtain ⟨nextGraph, step⟩ := OpenGraph.fill_first_exists graph context.dest (currentTree context sliceFor)
    (completedLeaf context sliceFor ordinal.toNat) ([] : List (BitVec 64 × Graph.Tree)) inv.aligned
  have leafStep : OpenGraph.FillFirst context.dest
      (.leaf (context.keyFor (BitVec.ofNat 64 ordinal.toNat)) (sliceFor (BitVec.ofNat 64 ordinal.toNat)))
      (completedLeaf context sliceFor ordinal.toNat) graph nextGraph := by
    rw [← treeEq]
    exact step
  have leafRep := fill_leaf_graph source layout context allocated 0 destination inv.atLayout valid inv.mapped branchRoom
    sliceFor inv.immutable ordinal.toNat ordinalBound graph nextGraph leafStep inv.represented inv.safe
  have closed : OpenGraph.frontier nextGraph = [] :=
    leaf_remaining context sliceFor [] graph nextGraph ordinal.toNat inv.aligned step
  obtain ⟨target, run, frame⟩ := terminal_body_finish source layout context allocated destination inv.atLayout valid inv.mapped branchRoom
    inv.locals inv.rows stop ordinal last
  let leafState := OpenGraph.leafPost source context.dest ordinal.toNat
  have memoryEq : leafState.memory = target.memory := (congrArg (fun state => state.memory) frame).symm
  have domainEq : leafState.memaddrs = target.memaddrs := (congrArg (fun state => state.memaddrs) frame).symm
  have endianEq : leafState.be = target.be := (congrArg (fun state => state.be) frame).symm
  have targetRep := OpenGraph.represents_of_agreement leafState target domainEq endianEq layout.table layout.keys layout.vals nextGraph
    (by intros; exact congrFun memoryEq _) leafRep.1
  obtain ⟨root, rootMapped, rootWord, represented,support⟩ := OpenGraph.completed_supported target layout.table layout.keys layout.vals nextGraph targetRep closed
  have rootEq : OpenGraph.slot nextGraph = cell layout .header 24 :=
    (OpenGraph.replacement_slot (OpenGraph.fill_replaces step) rfl).trans inv.root
  rw [rootEq] at rootMapped rootWord
  rw [leafRep.2.trans inv.expected] at represented support
  have leafFrontier:=leaf_frontier_update source layout context allocated 0 destination inv.atLayout valid branchRoom
    sliceFor inv.immutable ordinal.toNat ordinalBound graph nextGraph leafStep inv.located inv.safe inv.distinct
  have leafImmutable:=leaf_immutable source layout context allocated 0 destination inv.atLayout valid branchRoom sliceFor inv.immutable ordinal.toNat
  have targetImmutable:=immutable_of_agreement leafState target layout valid context.keyFor sliceFor domainEq endianEq
    (by intro query read;exact congrFun memoryEq query) leafImmutable
  refine ⟨target, root, run, frame, rootMapped, rootWord, represented,?_⟩
  intro query read
  have locatedRead:=located_reads target layout allocated valid context.keyFor sliceFor targetImmutable nextGraph leafFrontier.2.1
    query (support query read)
  rcases locatedRead with leaf|header|⟨node,nodeBound,field,fieldBound,equality⟩
  · exact Or.inl leaf
  · exact Or.inr (Or.inl header)
  · exact Or.inr (Or.inr ⟨node,by omega,field,fieldBound,equality⟩)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_terminal_finish_supported
