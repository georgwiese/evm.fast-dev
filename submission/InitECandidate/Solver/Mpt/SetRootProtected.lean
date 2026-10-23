import InitECandidate.Solver.Mpt.SetRootStore
import InitECandidate.Solver.Mpt.TrieProtectedWord

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real setter footer retains complete paths as well as structure
and values for a separated map header. Decoded nodes may precede the
header, and later inserted nodes may follow it. -/
theorem footer_graph_protected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m root : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) (mapped : source.memaddrs m)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower upper : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (word : graph.ProtectedWord m) :
    let target:=emptyLocalsHOLFinite (rootStored source m root)
    evaluateHOLFiniteState source footer=(some (.returned (.val (.word 0#64))),target) ∧ target.memory m=.word root ∧
      graph.PathFields target.memory ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  obtain ⟨fields,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=graph.after_protected_store source m root limit nodeLower pathLower upper property
    values regions disjoint paths pathRegions separated word
  exact ⟨footer_execute source m root mCell rootCell mapped,(by simp [rootStored,emptyLocalsHOLFinite,StoreWord.put]),fields,
    next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.footer_graph_protected
