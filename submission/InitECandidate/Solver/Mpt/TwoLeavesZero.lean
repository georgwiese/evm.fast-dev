import InitECandidate.Solver.Mpt.TwoLeavesProgram
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem zero_choice (second : Bool) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (choice second)=
      evaluateHOLFiniteState source (BranchValueUpdate.stores "br" (label second "v1" "v2") (label second "vl1" "vl2")) := by
  have read : eval source (.cmp .equal (localVar (label second "l1" "l2")) (.const 0#64))=some (.val (.word 1#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [(side_shapes second).1,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  simp

/-- Either actual zero-length side of the original helper installs its
branch value with the complete current graph and full path model intact. -/
theorem zero_side_paths (second : Bool) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (branch pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid branch) (active : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word 0#64)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (pointerCell : source.locals.lookup (ofString (label second "v1" "v2"))=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString (label second "vl1" "vl2"))=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size) :
    let post:=BranchValueUpdate.post source branch pointer size
    evaluateHOLFiniteState source (choice second)=(none,post) ∧
      ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
  let old:=values.branch branch member active notHash notLeaf notExtension
  have run:=BranchValueUpdate.stores_execute source branch pointer size "br" (label second "v1" "v2") (label second "vl1" "vl2")
    branchCell pointerCell sizeCell old.pointerMapped old.lengthMapped
  exact ⟨(zero_choice second source lengthCell).trans run,
    graph.after_branch_value_update source branch pointer size limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated
      member active notHash notLeaf notExtension payload extra⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.zero_choice
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.zero_side_paths
