import InitECandidate.Solver.Mpt.LeafUpdateGraph
import InitECandidate.Solver.Mpt.TriePathBytesLeafUpdate

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem compare_guard_shape : compareGuard=.ite (.cmp .notEqual (localVar "eq") (.const 0#64)) replaceBody .skip := by
  simp only [compareGuard,compareScope,lengthChoice,afterLength,afterKey,body,replaceBody,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

/-- A real return from this guard must have executed its replacement
stores. A skipped comparison cannot return the caller's value. -/
theorem compare_guard_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source compareGuard=(some (.returned value),post)) :
    evaluateHOLFiniteState source replaceBody=(some (.returned value),post) := by
  rw [compare_guard_shape,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) (.cmp .notEqual (localVar "eq") (.const 0#64))=read at normal
  cases read with
  | none=>cases normal
  | some read=>
    cases read with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        by_cases zero : word=0
        · have skipped : evaluateHOLFiniteState source .skip=(some (.returned value),post):=by simpa only [if_pos zero] using normal
          rw [evaluateHOLFiniteState_skip] at skipped
          cases skipped
        · exact (by simpa only [if_neg zero] using normal)

/-- The actual matching-return path of original249 returns the same
leaf, installs its bounded payload and retains the full current graph,
stored nibble buffers, allocation geometry and path/node separation. -/
theorem matching_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source compareGuard=(some (.returned value),target)) :
    value=.val (.word node) ∧ target=emptyLocalsHOLFinite (post source node pointer size) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have arena : AllocatedBytes.Arena node 64:=by simpa [leaf,TrieWalk.nodeBytes] using (regions node member active).2.1
  have aligned : node.toNat%8=0:=(regions node member active).2.2.1
  have expected:=replace_execute source node pointer size nodeCell pointerCell sizeCell domain arena aligned
  have same:=(compare_guard_return source target value normal).symm.trans expected
  have answer : value=.val (.word node):=by simpa only [Prod.mk.injEq,Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst same)
  have targetEq : target=emptyLocalsHOLFinite (post source node pointer size):=congrArg Prod.snd same
  obtain ⟨next,validEq,nextRegions,nextDisjoint,nextValues⟩:=graph.after_leaf_update source node pointer size limit lower upper property values regions disjoint member active leaf payload extra
  obtain ⟨nextPaths,nextPathRegions,nextSeparated⟩:=graph.leaf_update_path_models source node pointer size lower upper pathLower pathUpper regions disjoint paths pathRegions separated member active leaf next validEq
  refine ⟨answer,targetEq,?_⟩
  rw [targetEq]
  exact ⟨next,validEq,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_guard_shape
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_guard_return
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.matching_path_normal
