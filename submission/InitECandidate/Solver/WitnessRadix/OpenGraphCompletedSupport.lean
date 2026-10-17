import InitECandidate.Solver.WitnessRadix.OpenGraph

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

theorem closed_slot_read {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    (tree : Tree) (closed : frontier tree=[]) : reads source table keys vals tree (slot tree) := by
  cases tree with
  | hole address tree => simp [frontier] at closed
  | complete address root tree => exact Or.inl rfl
  | branch address node position zero one => exact Or.inl rfl

/-- Closing the actual construction graph retains its concrete read support,
in addition to the lookup representation. Later disjoint allocations can use
that support even when other memory contents differ. -/
theorem completed_supported {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    (tree : Tree) (rep : Represents source table keys vals tree) (closed : frontier tree=[]) :
    ∃ root : BitVec 64,source.memaddrs (slot tree) ∧ source.memory (slot tree)=.word root ∧
      QueryMemory.Represents source table keys vals root (expected tree) ∧
      (∀ query,QueryMemory.reads source table keys vals root (expected tree) query → reads source table keys vals tree query) := by
  induction tree with
  | hole address tree => simp [frontier] at closed
  | complete address root tree => exact ⟨root,rep.1,rep.2.1,rep.2.2,by intro query member;exact Or.inr member⟩
  | branch address node position zero one ihZero ihOne =>
    obtain ⟨mapped,word,nonzero,even,inside,nodeMapped,nodeWord,zeroSlot,oneSlot,zeroRep,oneRep⟩:=rep
    have zeroClosed : frontier zero=[]:=(List.append_eq_nil_iff.mp closed).1
    have oneClosed : frontier one=[]:=(List.append_eq_nil_iff.mp closed).2
    obtain ⟨zeroRoot,zeroMapped,zeroWord,zeroTree,zeroSupport⟩:=ihZero zeroRep zeroClosed
    obtain ⟨oneRoot,oneMapped,oneWord,oneTree,oneSupport⟩:=ihOne oneRep oneClosed
    rw [zeroSlot] at zeroMapped zeroWord
    rw [oneSlot] at oneMapped oneWord
    refine ⟨node,mapped,word,⟨nonzero,even,inside,nodeMapped,nodeWord,zeroMapped,oneMapped,
      zeroRoot,oneRoot,zeroWord,oneWord,zeroTree,oneTree⟩,?_⟩
    intro query member
    change QueryMemory.reads source table keys vals node (.branch position (expected zero) (expected one)) query at member
    simp only [QueryMemory.reads,zeroWord,oneWord,MemoryBytes.wordBits] at member
    rcases member with nodeRead|zeroRead|oneRead|zeroSubtree|oneSubtree
    · exact Or.inr (Or.inl nodeRead)
    · have childRead:=closed_slot_read source table keys vals zero zeroClosed
      rw [zeroSlot,←zeroRead] at childRead
      exact Or.inr (Or.inr (Or.inl childRead))
    · have childRead:=closed_slot_read source table keys vals one oneClosed
      rw [oneSlot,←oneRead] at childRead
      exact Or.inr (Or.inr (Or.inr childRead))
    · exact Or.inr (Or.inr (Or.inl (zeroSupport query zeroSubtree)))
    · exact Or.inr (Or.inr (Or.inr (oneSupport query oneSubtree)))

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.closed_slot_read
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.completed_supported
