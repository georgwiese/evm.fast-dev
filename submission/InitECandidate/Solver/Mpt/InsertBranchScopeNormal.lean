import InitECandidate.Solver.Mpt.InsertBranchDescend
import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original query-byte declaration derives a genuine index below16.
Its real branch descent and scope restoration leave an actual registered
next child/slot and consume exactly one more key nibble. -/
theorem branch_scope_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64) (notLeaf : wordAt source.memory node≠1#64) (notExtension : wordAt source.memory node≠2#64)
    (buffer : TrieWalk.NibbleSpan source.memory source.memaddrs source.be key length.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (before : level.toNat<length.toNat) (bounded : length.toNat≤64)
    (normal : evaluateHOLFiniteState source branchDescendScope=(none,target)) :
    ∃ index : Nat,index<16 ∧ ∃ child : BitVec 64,graph.valid child ∧ graph.ParentSlot (node+32#64+BitVec.ofNat 64 (index*8)) ∧
      (level+1#64).toNat=level.toNat+1 ∧ (level+1#64).toNat≤length.toNat ∧
      target=QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "r" node)
        "next_node" child) "next_slot" (node+32#64+BitVec.ofNat 64 (index*8))) "next_level" (level+1#64)) "go" 1#64 := by
  obtain ⟨nibble,small,byteRead⟩:=buffer.nibble level.toNat before
  have first : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (key+level)=some nibble:=by
    simpa [byteAddress] using byteRead
  have read : eval source branchIndex=some (.val (.word (BitVec.ofNat 64 nibble.toNat))):=by
    simp [eval,evalHOLExact,toExact,localVar,branchIndex,queryPointer,keyCell,levelCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,first]
  rw [branch_shapes.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "idx" branchIndex (BitVec.ofNat 64 nibble.toNat) branchDescend read normal
  let ready:=QueryBranch.bind source "idx" (BitVec.ofNat 64 nibble.toNat)
  have currentNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "idx" "node" _ (by decide)).trans nodeCell
  have currentLevel : ready.locals.lookup (ofString "level")=some (.val (.word level)):=
    (bind_lookup_other source "idx" "level" _ (by decide)).trans levelCell
  obtain ⟨child,childMember,selected,addition,nextBound,innerEq⟩:=branch_descend_normal ready inner node level length nibble.toNat small graph member active notHash notLeaf notExtension
    currentNode (bind_lookup_same source "idx" _) currentLevel before bounded continued
  refine ⟨nibble.toNat,small,child,childMember,selected,addition,nextBound,?_⟩
  rw [endpoint,innerEq]
  rw [restore_bind_other source _ "idx" "go" _ (by decide),restore_bind_other source _ "idx" "next_level" _ (by decide),
    restore_bind_other source _ "idx" "next_slot" _ (by decide),restore_bind_other source _ "idx" "next_node" _ (by decide),
    restore_bind_other source _ "idx" "r" _ (by decide),restore_bound]

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.branch_scope_normal
