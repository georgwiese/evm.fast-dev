import InitECandidate.Solver.WitnessRadix.OpenGraphFrontier
import InitECandidate.Solver.WitnessRadix.ReadFootprintStable

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

def SafeFrontier {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64) (tree : Tree) : Prop :=
  ∀ entry ∈ frontier tree, ¬ reads source table keys vals tree entry.1

theorem replacement_reads {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : ReplaceHole address tree replacement before after) (query : BitVec 64) :
    reads source table keys vals after query ↔
      reads source table keys vals before query ∨ reads source table keys vals replacement query := by
  induction step with
  | here => simp only [reads, false_or]
  | zero step ih => simp only [reads, ih]; tauto
  | one step ih => simp only [reads, ih]; tauto

/-- Frontier stores remain safe after filling the first hole. New child slots
must be fresh, and installed reads must avoid all other pending hole slots. -/
theorem fill_safe {F : Type} (source target : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : FillFirst address tree replacement before after)
    (distinct : ((frontier before).map Prod.fst).Nodup)
    (safe : SafeFrontier source table keys vals before)
    (agree : ∀ query, reads source table keys vals before query → source.memory query = target.memory query)
    (newSafe : SafeFrontier target table keys vals replacement)
    (newFresh : ∀ entry ∈ frontier replacement, ¬ reads source table keys vals before entry.1)
    (pendingAway : ∀ entry ∈ frontier before, entry.1 ≠ address →
      ¬ reads target table keys vals replacement entry.1) :
    SafeFrontier target table keys vals after := by
  obtain ⟨pending, oldFrontier, newFrontier⟩ := fill_frontier step
  have addressAbsent : address ∉ pending.map Prod.fst := by
    rw [oldFrontier, List.map_cons, List.nodup_cons] at distinct
    exact distinct.1
  intro entry member read
  have either := (replacement_reads target table keys vals (fill_replaces step) entry.1).mp read
  rw [newFrontier] at member
  rcases List.mem_append.mp member with newMember | oldMember
  · rcases either with oldRead | newRead
    · exact newFresh entry newMember ((reads_stable source target table keys vals before agree entry.1).mpr oldRead)
    · exact newSafe entry newMember newRead
  · have wasMember : entry ∈ frontier before := by
      rw [oldFrontier]
      exact List.mem_cons_of_mem _ oldMember
    have different : entry.1 ≠ address := by
      intro same
      exact addressAbsent (List.mem_map.mpr ⟨entry, oldMember, same⟩)
    rcases either with oldRead | newRead
    · exact safe entry wasMember ((reads_stable source target table keys vals before agree entry.1).mpr oldRead)
    · exact pendingAway entry wasMember different newRead

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.replacement_reads
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.fill_safe
