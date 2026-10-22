import InitECandidate.Solver.Mpt.SetEmptyDispatch
import InitECandidate.Solver.Mpt.TrieGraphStorageFrame

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rootStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m root : BitVec 64):=
  {source with memory:=StoreWord.put source.memory m root}

theorem footer_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m root : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) (mapped : source.memaddrs m) :
    evaluateHOLFiniteState source footer=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (rootStored source m root)) := by
  have address : eval source (addConst (localVar "m") 0#64)=some (.val (.word m)):=by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value : eval source (localVar "root")=some (.val (.word root)):=by simp [eval,localVar,evalHOLExact,toExact,rootCell]
  have stored:=StoreWord.execute source (addConst (localVar "m") 0#64) (localVar "root") m root address value mapped
  rw [mutation_shapes.2.2.2,evaluateHOLFiniteState_seq_line780,stored]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,rootStored]

/-- Updating an older trie object's root cannot overwrite its newer
registered node fields. The actual store retains graph, values and real
allocation geometry, then the original return clears only caller locals. -/
theorem footer_graph (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m root : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) (mapped : source.memaddrs m)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit lower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (older : m.toNat<lower) :
    let target:=emptyLocalsHOLFinite (rootStored source m root)
    evaluateHOLFiniteState source footer=(some (.returned (.val (.word 0#64))),target) ∧ target.memory m=.word root ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) := by
  let target:=emptyLocalsHOLFinite (rootStored source m root)
  have memory (query : BitVec 64) (after : lower≤query.toNat) : target.memory query=source.memory query:=by
    have different : query≠m:=by intro same; have equal:=congrArg BitVec.toNat same; omega
    simp [target,rootStored,emptyLocalsHOLFinite,StoreWord.put,different]
  have retained:=graph.after_agreement source target limit lower upper property values regions disjoint rfl
    (fun query required=>memory query (graph.footprint_bounds lower upper regions query required).1)
    (fun query required=>memory query (graph.value_bounds lower upper regions query required).1)
  exact ⟨footer_execute source m root mCell rootCell mapped,by simp [target,rootStored,emptyLocalsHOLFinite,StoreWord.put],retained⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.footer_execute
#print axioms InitECandidate.Solver.Mpt.SetTrie.footer_graph
