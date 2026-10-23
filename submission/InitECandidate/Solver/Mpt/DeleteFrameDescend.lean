import InitECandidate.Solver.Mpt.DeleteFrameAdvance
import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original extension push advances to its actual registered child.
Its stored positive segment, bounded by the matched remaining query,
strictly increases the real level even when that child is an ancestor. -/
theorem extension_descend_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record node level length segmentLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64) (paths : graph.PathBytes source.be)
    (lengthEq : segmentLength=wordAt source.memory (node+40#64))
    (recordCell : source.locals.lookup (ofString "fr")=some (.val (.word record)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (segmentCell : source.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
    (within : level.toNat≤length.toNat) (matched : segmentLength.toNat≤length.toNat-level.toNat) (small : length.toNat≤64)
    (normal : evaluateHOLFiniteState source (Kind.advance .extension)=(none,target)) :
    ∃ child : BitVec 64,graph.valid child ∧ target=advanced source record child (level+segmentLength) ∧
      (level+segmentLength).toNat=level.toNat+segmentLength.toNat ∧
      level.toNat<(level+segmentLength).toNat ∧ (level+segmentLength).toNat≤length.toNat := by
  let child:=graph.extension node member active tag
  let first:=QueryBranch.bind source "top" record
  let second:=QueryBranch.bind first "node" child.child
  have currentNode : first.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "top" "node" record (by decide)).trans nodeCell
  have childRead : eval first (Kind.childExpression .extension)=some (.val (.word child.child)):=
    DeleteExtension.field_read first "node" node 48#64 child.child currentNode child.mapped child.stored
  have currentLevel : second.locals.lookup (ofString "level")=some (.val (.word level)):=
    (bind_lookup_other first "node" "level" child.child (by decide)).trans
      ((bind_lookup_other source "top" "level" record (by decide)).trans levelCell)
  have currentSegment : second.locals.lookup (ofString "sl")=some (.val (.word segmentLength)):=
    (bind_lookup_other first "node" "sl" child.child (by decide)).trans
      ((bind_lookup_other source "top" "sl" record (by decide)).trans segmentCell)
  have levelRead : eval second (Kind.levelExpression .extension)=some (.val (.word (level+segmentLength))):=by
    simp [Kind.levelExpression,eval,localVar,evalHOLExact,evalListHOLExact,toExact,currentLevel,currentSegment,valueIsWord,valueWord,wordOpHOL,wordOp]
  have endpoint:=advance_normal .extension source target record child.child (level+segmentLength) recordCell childRead levelRead normal
  have positive : 0<segmentLength.toNat:=by rw [lengthEq]; exact paths.positive node member active tag
  obtain ⟨addition,increases,before⟩:=extension_progress level length segmentLength positive matched within small
  exact ⟨child.child,child.member,endpoint,addition,increases,before⟩

/-- The original branch push selects its actual mapped child slot and
consumes exactly one query nibble; no child-pointer order is assumed. -/
theorem branch_descend_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record node level length : BitVec 64) (index : Nat) (smallIndex : index<16)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64) (notLeaf : wordAt source.memory node≠1#64) (notExtension : wordAt source.memory node≠2#64)
    (recordCell : source.locals.lookup (ofString "fr2")=some (.val (.word record)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (before : level.toNat<length.toNat) (small : length.toNat≤64)
    (normal : evaluateHOLFiniteState source (Kind.advance .branch)=(none,target)) :
    ∃ child : BitVec 64,graph.valid child ∧ target=advanced source record child (level+1#64) ∧
      (level+1#64).toNat=level.toNat+1 ∧ level.toNat<(level+1#64).toNat ∧ (level+1#64).toNat≤length.toNat := by
  let child:=graph.branch node member active notHash notLeaf notExtension index smallIndex
  let first:=QueryBranch.bind source "top" record
  let second:=QueryBranch.bind first "node" child.child
  have currentNode : first.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "top" "node" record (by decide)).trans nodeCell
  have currentIndex : first.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))):=
    (bind_lookup_other source "top" "idx" record (by decide)).trans indexCell
  have product : BitVec.ofNat 64 index*8#64=BitVec.ofNat 64 (index*8):=by rw [BitVec.ofNat_mul]
  have currentMapped : first.memaddrs (node+32#64+BitVec.ofNat 64 (index*8)):=child.mapped
  have currentStored : first.memory (node+32#64+BitVec.ofNat 64 (index*8))=.word child.child:=child.stored
  have childRead : eval first (Kind.childExpression .branch)=some (.val (.word child.child)):=by
    simp [Kind.childExpression,DeleteBody.childAddress,eval,localVar,evalHOLExact,evalListHOLExact,toExact,currentNode,currentIndex,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,←BitVec.add_assoc]
    rw [memLoadHOLExact.eq_1,if_pos currentMapped,currentStored]
  have currentLevel : second.locals.lookup (ofString "level")=some (.val (.word level)):=
    (bind_lookup_other first "node" "level" child.child (by decide)).trans
      ((bind_lookup_other source "top" "level" record (by decide)).trans levelCell)
  have levelRead : eval second (Kind.levelExpression .branch)=some (.val (.word (level+1#64))):=by
    simp [Kind.levelExpression,eval,localVar,evalHOLExact,evalListHOLExact,toExact,currentLevel,valueIsWord,valueWord,wordOpHOL,wordOp]
  have endpoint:=advance_normal .branch source target record child.child (level+1#64) recordCell childRead levelRead normal
  obtain ⟨addition,increases,bounded⟩:=branch_progress level length before small
  exact ⟨child.child,child.member,endpoint,addition,increases,bounded⟩

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.extension_descend_normal
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.branch_descend_normal
