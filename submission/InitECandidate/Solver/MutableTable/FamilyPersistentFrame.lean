import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact

/-- A current persistent word lies outside every live table pool. Records
may sit between pools; they need not precede all table lifetime floors. -/
def Outside {ι : Type} (objects : ι → Object) (query : BitVec 64) : Prop :=
  ∀ index,TableFootprint.Outside (objects index).kind (objects index).plan query

/-- Retain earlier non-table words above scratch, together with their
separation from any actual relocated table pools. -/
structure PersistentFrame {ι : Type} (cutoff cursor : Nat) (objects next : ι → Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  words : ∀ query : BitVec 64,cutoff≤query.toNat → query.toNat<cursor → Outside objects query →
    Outside next query ∧ target.memory query=source.memory query

theorem PersistentFrame.refl {ι : Type} (cutoff cursor : Nat) (objects : ι → Object) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    PersistentFrame cutoff cursor objects objects source source := ⟨fun query lower earlier outside=>⟨outside,rfl⟩⟩

theorem PersistentFrame.of_memory {ι : Type} (cutoff cursor : Nat) (objects : ι → Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : target.memory=source.memory) :
    PersistentFrame cutoff cursor objects objects source target := ⟨fun query lower earlier outside=>⟨outside,congrFun memory query⟩⟩

theorem PersistentFrame.trans {ι : Type} {cutoff cursor middleCursor : Nat} {objects middleObjects next : ι → Object}
    {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : PersistentFrame cutoff cursor objects middleObjects source middle)
    (second : PersistentFrame cutoff middleCursor middleObjects next middle target) (forward : cursor≤middleCursor) :
    PersistentFrame cutoff cursor objects next source target := by
  constructor
  intro query lower earlier outside
  have firstStep := first.words query lower earlier outside
  have secondStep := second.words query lower (by omega) firstStep.1
  exact ⟨secondStep.1,secondStep.2.trans firstStep.2⟩

/-- The actual setter's proved earlier-word footprint lifts to the entire
family, even when the writer relocates its arrays past unrelated records. -/
theorem PersistentFrame.of_set {ι : Type} [DecidableEq ι] (cutoff cursor : Nat) (objects : ι → Object) (writer : ι) (next : Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (earlier : ∀ query : BitVec 64,query.toNat<cursor → TableFootprint.Outside (objects writer).kind (objects writer).plan query →
      TableFootprint.Outside next.kind next.plan query ∧ target.memory query=source.memory query) :
    PersistentFrame cutoff cursor objects (Function.update objects writer next) source target := by
  constructor
  intro query lower before outside
  have changed := earlier query before (outside writer)
  refine ⟨?_,changed.2⟩
  intro index
  by_cases same : index=writer
  · subst index
    simpa only [Function.update_self] using changed.1
  · rw [Function.update_of_ne same]
    exact outside index

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.PersistentFrame.refl
#print axioms InitECandidate.Solver.MutableTable.TableFamily.PersistentFrame.of_memory
#print axioms InitECandidate.Solver.MutableTable.TableFamily.PersistentFrame.trans
#print axioms InitECandidate.Solver.MutableTable.TableFamily.PersistentFrame.of_set
