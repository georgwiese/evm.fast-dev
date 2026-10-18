import InitECandidate.Solver.MutableTable.SetModelOwnership

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- An actual setter preserves separation from an earlier live reader.
Growth retains the old separated header and allocates every replacement
array beyond the reader's pools. Old array order need not be uniform. -/
theorem ModelPost.reader_separate {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old plan : Plan}
    {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}
    (post : ModelPost source kind old start count paid globals memory target plan slots)
    (readerKind : KeyHash.Kind) (reader : Plan)
    (earlier : ∀ pool, reader.base pool + size readerKind reader pool ≤ start)
    (apart : ∀ first second, old.base first + size kind old first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ old.base first) :
    ∀ first second, plan.base first + size kind plan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ plan.base first := by
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact apart
  · intro first second
    by_cases header : first = .header
    · subst first
      exact apart .header second
    · right
      have before := earlier second
      have after : start ≤ (relocated kind (old.base .header) start (2 * old.capacity)).base first := by
        cases first with
        | header => exact (header rfl).elim
        | keys => exact Nat.le_refl _
        | values => simp only [relocated]; omega
        | used => simp only [relocated]; omega
        | order => simp only [relocated]; omega
        | position => simp only [relocated]; omega
      omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.reader_separate
