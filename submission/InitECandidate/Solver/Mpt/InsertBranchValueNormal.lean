import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph
import InitECandidate.Solver.Mpt.TriePathBufferMutation
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- At the end of a key, the real branch value writes retain its closed
children, all other bounded values, complete paths and caller buffers. -/
theorem branch_value_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower nodeUpper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower nodeUpper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64) (notLeaf : wordAt source.memory node≠1#64) (notExtension : wordAt source.memory node≠2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (normal : evaluateHOLFiniteState source branchValue=(none,target)) :
    target=QueryBranch.bind (BranchValueUpdate.post source node pointer size) "r" node ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nodeUpper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated ∧
        ∀ key length,graph.PathBuffer source.be pathLower pathUpper key length → next.PathBuffer target.be pathLower pathUpper key length := by
  let old:=values.branch node member active notHash notLeaf notExtension
  have shape : branchValue=BranchValueUpdate.program "node" "vptr" "vlen" pointer size (.assign .local (ofString "r") (localVar "node")):=by
    rw [branch_shapes.2.1]
    rfl
  rw [shape,BranchValueUpdate.execute source node pointer size "node" "vptr" "vlen" _ nodeCell pointerCell sizeCell old.pointerMapped old.lengthMapped] at normal
  have read : eval (BranchValueUpdate.post source node pointer size) (localVar "node")=some (.val (.word node)):=by
    simp [eval,evalHOLExact,toExact,localVar,BranchValueUpdate.post,nodeCell]
  have endpoint:=Input.assign_none (BranchValueUpdate.post source node pointer size) target "r" (localVar "node") node read normal
  refine ⟨endpoint,?_⟩
  rw [endpoint]
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    graph.after_branch_value_update source node pointer size limit nodeLower nodeUpper pathLower pathUpper property values regions disjoint paths pathRegions separated member active notHash notLeaf notExtension payload extra
  have tags (current : BitVec 64) (live : graph.valid current) (nonzero : current≠0#64) : wordAt (BranchValueUpdate.post source node pointer size).memory current=wordAt source.memory current:=by
    have away:=graph.branch_value_away nodeLower nodeUpper regions disjoint node current member active notHash notLeaf notExtension (.header current live nonzero)
    unfold wordAt
    rw [BranchValueUpdate.post_away source node pointer size current away.1 away.2]
  have olderMemory (query : BitVec 64) (before : query.toNat<nodeLower) : (BranchValueUpdate.post source node pointer size).memory query=source.memory query:=by
    have bounds:=regions node member active
    have nodeSize : TrieWalk.nodeBytes (wordAt source.memory node)=176:=by simp [TrieWalk.nodeBytes,notHash,notLeaf,notExtension]
    have away (offset : Nat) (inside : offset<176) : query≠byteAddress node offset:=by
      intro equal
      have number:=congrArg BitVec.toNat equal
      rw [byteAddress_toNat node offset (by have upper:=bounds.2.1.upper; rw [nodeSize] at upper; omega)] at number
      omega
    exact BranchValueUpdate.post_away source node pointer size query (away 160 (by decide)) (away 168 (by decide))
  exact ⟨olderMemory,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
    by intro key length buffer; exact buffer.after_branch_value_update source graph nodeLower nodeUpper pathLower pathUpper key length regions disjoint node pointer size member active notHash notLeaf notExtension next same⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.branch_value_normal
