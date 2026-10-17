import InitECandidate.Solver.WitnessRadix.OpenGraph

namespace InitECandidate.Solver.WitnessRadix.QueryMemory
open Flapjack PanSemStateFiniteExact

theorem reads_stable {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (table keys vals root : BitVec 64) (tree : Graph.Tree)
    (agree : ∀ query, reads source table keys vals root tree query → source.memory query = target.memory query)
    (query : BitVec 64) :
    reads source table keys vals root tree query ↔ reads target table keys vals root tree query := by
  induction tree generalizing root query with
  | empty => rfl
  | leaf key value =>
      have recordEq := agree (vals + (root >>> (1 : Nat)) * 8#64) (Or.inr (Or.inr (Or.inl rfl)))
      simp only [reads, recordEq]
  | branch position zero one ihZero ihOne =>
      have zeroEq := agree (root + 8#64) (Or.inr (Or.inl rfl))
      have oneEq := agree (root + 16#64) (Or.inr (Or.inr (Or.inl rfl)))
      have zeroAgree : ∀ address, reads source table keys vals (MemoryBytes.wordBits (source.memory (root + 8#64))) zero address →
          source.memory address = target.memory address :=
        fun address member => agree address (Or.inr (Or.inr (Or.inr (Or.inl member))))
      have oneAgree : ∀ address, reads source table keys vals (MemoryBytes.wordBits (source.memory (root + 16#64))) one address →
          source.memory address = target.memory address :=
        fun address member => agree address (Or.inr (Or.inr (Or.inr (Or.inr member))))
      simp only [reads, ← zeroEq, ← oneEq]
      exact or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl
        (or_congr (ihZero _ zeroAgree query) (ihOne _ oneAgree query))))

end InitECandidate.Solver.WitnessRadix.QueryMemory

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

theorem reads_stable {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (table keys vals : BitVec 64) (tree : Tree)
    (agree : ∀ query, reads source table keys vals tree query → source.memory query = target.memory query)
    (query : BitVec 64) : reads source table keys vals tree query ↔ reads target table keys vals tree query := by
  induction tree with
  | hole address tree => rfl
  | complete address root tree =>
      exact or_congr Iff.rfl (QueryMemory.reads_stable source target table keys vals root tree
        (fun query member => agree query (Or.inr member)) query)
  | branch address node position zero one ihZero ihOne =>
      exact or_congr Iff.rfl (or_congr Iff.rfl (or_congr
        (ihZero (fun query member => agree query (Or.inr (Or.inr (Or.inl member)))))
        (ihOne (fun query member => agree query (Or.inr (Or.inr (Or.inr member)))))))

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.QueryMemory.reads_stable
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.reads_stable
