import InitECandidate.Solver.Mpt.TrieWalkLeafValues
import InitECandidate.Solver.Input.ReturnFactsScalar
import InitECandidate.Solver.Input.ReturnFactsScopedAny

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem extension_advance_prefix : Input.LocalPrefix (ofString "nibs") extensionAdvance := by
  rw [extension_advance_shape]
  exact .seq (.assign _ _ (by decide)) (.assign _ _ (by decide))

theorem after_compare_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : BitVec 64 → Prop) (limit : Nat) :
    Returns source afterCompare (Answer domain limit (property:=property)) := by
  rw [after_compare_shape]
  apply Input.ReturnFacts.sequence
  · rw [comparison_guard_shape]
    exact Input.ReturnFacts.conditional source _ _ _ _ (absent_returns source domain limit) (Input.ReturnFacts.skip source _)
  · intro middle normal
    exact Input.ReturnFacts.local_prefix middle (ofString "nibs") extensionAdvance extension_advance_prefix _

theorem extension_compare_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : BitVec 64 → Prop) (limit : Nat) :
    Returns source extensionCompare (Answer domain limit (property:=property)) := by
  rw [compare_shape]
  exact Input.ReturnFacts.scoped_any source "eq2" .one (ofString "memeq") compareArguments afterCompare _
    (fun ready => after_compare_returns ready domain limit)

/-- Extensions only return an absent value or continue the walk. This
classification does not assume successful comparisons or child reads. -/
theorem extension_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : BitVec 64 → Prop) (limit : Nat) :
    Returns source extension (Answer domain limit (property:=property)) := by
  rw [extension_shape]
  apply Input.ReturnFacts.declared
  intro value
  let entered := setVarHOLFinite (ofString "sl") value source
  apply Input.ReturnFacts.sequence
  · rw [extent_guard_shape]
    exact Input.ReturnFacts.conditional entered _ _ _ _ (absent_returns entered domain limit) (Input.ReturnFacts.skip entered _)
  · intro middle normal
    exact extension_compare_returns middle domain limit

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_advance_prefix
#print axioms InitECandidate.Solver.Mpt.TrieWalk.after_compare_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_compare_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_returns
