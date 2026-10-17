import InitECandidate.Solver.WitnessRadix.OpenGraph

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

/-- Replace one frontier hole while retaining every ancestor and sibling. -/
inductive ReplaceHole (address : BitVec 64) (tree : Graph.Tree) (replacement : Tree) : Tree → Tree → Prop
  | here : ReplaceHole address tree replacement (.hole address tree) replacement
  | zero {slot node position zero zeroNext one}
      (next : ReplaceHole address tree replacement zero zeroNext) :
      ReplaceHole address tree replacement (.branch slot node position zero one) (.branch slot node position zeroNext one)
  | one {slot node position zero one oneNext}
      (next : ReplaceHole address tree replacement one oneNext) :
      ReplaceHole address tree replacement (.branch slot node position zero one) (.branch slot node position zero oneNext)

theorem replacement_slot {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : ReplaceHole address tree replacement before after) (same : slot replacement = address) :
    slot after = slot before := by
  cases step with
  | here => exact same
  | zero => rfl
  | one => rfl

theorem replacement_expected {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : ReplaceHole address tree replacement before after) (same : expected replacement = tree) :
    expected after = expected before := by
  induction step with
  | here => exact same
  | zero step ih => simp only [expected, ih]
  | one step ih => simp only [expected, ih]

/-- The write-side obligation is only agreement on established reads; the
new subtree is checked separately at the selected formerly unconstrained hole. -/
theorem replacement_represents {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (table keys vals : BitVec 64) {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : ReplaceHole address tree replacement before after) (same : slot replacement = address)
    (newRep : Represents target table keys vals replacement)
    (agree : ∀ query, reads source table keys vals before query → source.memory query = target.memory query)
    (oldRep : Represents source table keys vals before) : Represents target table keys vals after := by
  induction step with
  | here => exact newRep
  | @zero address' node position zero zeroNext one step ih =>
      rcases oldRep with ⟨mapped, word, nonzero, even, inside, nodeMapped, nodeWord, zeroSlot, oneSlot, zeroRep, oneRep⟩
      rw [domain] at mapped nodeMapped
      refine ⟨mapped, (agree _ (Or.inl rfl)).symm.trans word, nonzero, even, inside, nodeMapped,
        (agree _ (Or.inr (Or.inl rfl))).symm.trans nodeWord,
        (replacement_slot step same).trans zeroSlot, oneSlot, ?_, ?_⟩
      · exact ih (fun query member => agree query (Or.inr (Or.inr (Or.inl member)))) zeroRep
      · exact represents_of_agreement source target domain endian table keys vals one
          (fun query member => agree query (Or.inr (Or.inr (Or.inr member)))) oneRep
  | @one address' node position zero one oneNext step ih =>
      rcases oldRep with ⟨mapped, word, nonzero, even, inside, nodeMapped, nodeWord, zeroSlot, oneSlot, zeroRep, oneRep⟩
      rw [domain] at mapped nodeMapped
      refine ⟨mapped, (agree _ (Or.inl rfl)).symm.trans word, nonzero, even, inside, nodeMapped,
        (agree _ (Or.inr (Or.inl rfl))).symm.trans nodeWord, zeroSlot,
        (replacement_slot step same).trans oneSlot, ?_, ?_⟩
      · exact represents_of_agreement source target domain endian table keys vals zero
          (fun query member => agree query (Or.inr (Or.inr (Or.inl member)))) zeroRep
      · exact ih (fun query member => agree query (Or.inr (Or.inr (Or.inr member)))) oneRep

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.replacement_expected
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.replacement_represents
