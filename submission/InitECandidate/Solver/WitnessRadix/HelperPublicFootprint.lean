import InitECandidate.Solver.WitnessRadix.LoopTermination

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact SplitScope

/-- A public word is outside every mutable radix-helper cell. Immutable
record and hash words need not be excluded from the public region. -/
def PublicWord (layout : Layout) (query : BitVec 64) : Prop :=
  ∀ pool offset, WriteOffset layout pool offset → query ≠ cell layout pool offset

theorem leaf_public {F : Type} (source : PanSemStateFiniteExact 64 F)
    (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (branchRoom : allocated < layout.count)
    (ordinal : Nat) (query : BitVec 64) (publicWord : PublicWord layout query) :
    (OpenGraph.leafPost source context.dest ordinal).memory query = source.memory query := by
  change StoreWord.put source.memory context.dest _ query = _
  apply if_neg
  rw [atLayout.destEq]
  exact publicWord destination.1 destination.2 (incoming_write layout allocated branchRoom destination atLayout.incoming)

theorem resume_public {F : Type} (source : PanSemStateFiniteExact 64 F)
    (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (branchRoom : allocated < layout.count)
    (task : PendingStack.Task) (ordinal : Nat) (query : BitVec 64) (publicWord : PublicWord layout query) :
    (resumePost source context task ordinal).memory query = source.memory query :=
  leaf_public source layout context allocated depth destination atLayout branchRoom ordinal query publicWord

theorem unary_public {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (query : BitVec 64) :
    (unaryPost source context).memory query = source.memory query := rfl

theorem split_public {F : Type} (source : PanSemStateFiniteExact 64 F)
    (layout : Layout) (valid : Valid layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (query : BitVec 64) (publicWord : PublicWord layout query) :
    (SplitCount.post source context).memory query = source.memory query := by
  have room := valid.room
  apply SplitCount.post_away
  · intro offset inside
    rw [atLayout.srcEq]
    change query ≠ BuildCopy.row (base layout .primary) _ _
    rw [row_cell]
    exact publicWord .primary (8 * (context.start + offset))
      ⟨context.start + offset, by have := atLayout.interval; omega, rfl⟩
  · intro offset inside
    rw [atLayout.dstEq]
    change query ≠ BuildCopy.row (base layout .backup) _ _
    rw [row_cell]
    exact publicWord .backup (8 * (context.start + offset))
      ⟨context.start + offset, by have := atLayout.interval; omega, rfl⟩
  · intro member
    obtain ⟨pool, offset, writable, same⟩ := allocation_writable layout context allocated depth destination atLayout valid
      branchRoom stackRoom query member
    exact publicWord pool offset writable same

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_public
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.resume_public
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.unary_public
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_public
