import InitECandidate.Solver.WitnessRadix.InitialContext

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def initialTree (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) (input : List (BitVec 64)) : Graph.Tree :=
  buildIndex ByteKeys.bit 256 (OrdinalTree.entries keyFor sliceFor input)

def initialGraph (layout : Layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (input : List (BitVec 64)) : OpenGraph.Tree := .hole (cell layout .header 24) (initialTree keyFor sliceFor input)

/-- Actual entered locals and existing backing arrays establish the entire
loop invariant, before any branch or pending task has been created. -/
theorem invariant_initial {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) (input : List (BitVec 64))
    (length : input.length = layout.count) (present : input ≠ [])
    (ordinals : ∀ ordinal ∈ input, ordinal.toNat < layout.count)
    (mapped : Mapped source layout) (immutable : Immutable source layout keyFor sliceFor)
    (rows : BuildCopy.Rows source.memory source.memaddrs layout.primary 0#64 0 input) :
    Invariant (initialState source layout) layout sliceFor (initialTree keyFor sliceFor input) 0 0 0
      (initialContext layout keyFor input) (.header, 24) [] (initialGraph layout keyFor sliceFor input) := by
  let target := initialState source layout
  have rootMapped : target.memaddrs (cell layout .header 24) := mapped .header 24 (by decide) (by change 24 + 8 ≤ 72; decide)
  have mappedPresent : (input.map fun ordinal => (ordinal, ())).length = input.length := List.length_map _
  have entriesPresent : (input.map fun ordinal => (ordinal, ())) ≠ [] := by
    intro empty
    exact present (List.eq_nil_of_map_eq_nil empty)
  refine ⟨mapped,
    immutable_of_agreement source target layout valid keyFor sliceFor rfl rfl (by intros; rfl) immutable,
    initial_layout layout keyFor input length ordinals, initial_locals source layout keyFor input length,
    rows, present, (by change 0 ≤ 256; decide), rfl, (by intro task member; cases member),
    (by intro task member; cases member), True.intro, (by intro task member; cases member), True.intro,
    rootMapped, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · exact ⟨.header, 24, rfl, rfl⟩
  · intro entry member read
    exact False.elim read
  · simp [initialGraph, OpenGraph.frontier]
  · have budget := initial_frontier_budget (input.map fun ordinal => (ordinal, ())) entriesPresent 0 256
    rw [mappedPresent, length] at budget
    exact budget

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_initial
