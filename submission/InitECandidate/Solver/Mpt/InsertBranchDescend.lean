import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.TrieParentSlot
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original branch descent reads its real registered child and
performs its five scalar assignments. Its next slot is a real child slot
and its consumed key length increases without wrapping. -/
theorem branch_descend_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node level length : BitVec 64) (index : Nat) (small : index<16)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64) (notLeaf : wordAt source.memory node≠1#64) (notExtension : wordAt source.memory node≠2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (before : level.toNat<length.toNat) (bounded : length.toNat≤64)
    (normal : evaluateHOLFiniteState source branchDescend=(none,target)) :
    ∃ child : BitVec 64,graph.valid child ∧ graph.ParentSlot (node+32#64+BitVec.ofNat 64 (index*8)) ∧
      (level+1#64).toNat=level.toNat+1 ∧ (level+1#64).toNat≤length.toNat ∧
      target=QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "r" node)
        "next_node" child) "next_slot" (node+32#64+BitVec.ofNat 64 (index*8))) "next_level" (level+1#64)) "go" 1#64 := by
  classical
  simp [ofString] at nodeCell indexCell levelCell
  let child:=graph.branch node member active notHash notLeaf notExtension index small
  let first:=QueryBranch.bind source "r" node
  let second:=QueryBranch.bind first "next_node" child.child
  let third:=QueryBranch.bind second "next_slot" (node+32#64+BitVec.ofNat 64 (index*8))
  let fourth:=QueryBranch.bind third "next_level" (level+1#64)
  have product : BitVec.ofNat 64 index*8#64=BitVec.ofNat 64 (index*8):=by rw [BitVec.ofNat_mul]
  have rRead : eval source (localVar "node")=some (.val (.word node)):=by simp [eval,evalHOLExact,toExact,localVar,ofString,nodeCell]
  have childRead : eval first (.load .one branchChildAddress)=some (.val (.word child.child)):=by
    simp [eval,evalHOLExact,toExact,localVar,branchChildAddress,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      nodeCell,indexCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,←BitVec.add_assoc]
    rw [memLoadHOLExact.eq_1,if_pos child.mapped,child.stored]
  have slotRead : eval second branchChildAddress=some (.val (.word (node+32#64+BitVec.ofNat 64 (index*8)))):=by
    simp [eval,evalHOLExact,toExact,localVar,branchChildAddress,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      nodeCell,indexCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,←BitVec.add_assoc]
  have levelRead : eval third (.op .add [localVar "level",.const 1#64])=some (.val (.word (level+1#64))):=by
    simp [eval,evalHOLExact,toExact,localVar,third,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      levelCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [branch_shapes.2.2.2] at normal
  obtain ⟨one,rRun,tailRun⟩:=Input.sequence_none source target _ _ normal
  have oneEq : one=first:=Input.assign_none source one "r" _ node rRead rRun
  subst one
  obtain ⟨two,nRun,tailRun⟩:=Input.sequence_none first target _ _ tailRun
  have twoEq : two=second:=Input.assign_none first two "next_node" _ child.child childRead nRun
  subst two
  obtain ⟨three,sRun,tailRun⟩:=Input.sequence_none second target _ _ tailRun
  have threeEq : three=third:=Input.assign_none second three "next_slot" _ _ slotRead sRun
  subst three
  obtain ⟨four,lRun,gRun⟩:=Input.sequence_none third target _ _ tailRun
  have fourEq : four=fourth:=Input.assign_none third four "next_level" _ _ levelRead lRun
  subst four
  have endpoint:=Input.assign_none fourth target "go" (.const 1#64) 1#64 rfl gRun
  have addition : (level+1#64).toNat=level.toNat+1:=by
    have numeric:=BitVec.toNat_add_of_lt (x:=level) (y:=1#64) (by change level.toNat+1<2^64; omega)
    exact numeric
  refine ⟨child.child,child.member,Or.inr ⟨node,32+index*8,member,active,.branch notHash notLeaf notExtension index small,?_⟩,addition,?_,endpoint⟩
  · simp [BitVec.ofNat_add,BitVec.add_assoc]
  · rw [addition]; omega

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.branch_descend_normal
