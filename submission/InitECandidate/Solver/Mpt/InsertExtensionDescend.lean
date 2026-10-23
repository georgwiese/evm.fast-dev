import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.TrieParentSlot
import InitECandidate.Solver.Mpt.TrieGraphPathBytes
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original matching extension descends through its real child.
Positive full stored path length makes the consumed key length increase,
even if the registered graph contains a cycle. -/
theorem extension_descend_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node level length prefixLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64) (paths : graph.PathBytes source.be)
    (matched : prefixLength=wordAt source.memory (node+40#64))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (before : level.toNat+prefixLength.toNat≤length.toNat) (bounded : length.toNat≤64)
    (normal : evaluateHOLFiniteState source extensionDescend=(none,target)) :
    ∃ child : BitVec 64,graph.valid child ∧ graph.ParentSlot (node+48#64) ∧
      (level+prefixLength).toNat=level.toNat+prefixLength.toNat ∧ (level+prefixLength).toNat≤length.toNat ∧ level.toNat<(level+prefixLength).toNat ∧
      target=QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "r" node)
        "next_node" child) "next_slot" (node+48#64)) "next_level" (level+prefixLength)) "go" 1#64 := by
  classical
  simp [ofString] at nodeCell prefixCell levelCell
  let child:=graph.extension node member active tag
  let first:=QueryBranch.bind source "r" node
  let second:=QueryBranch.bind first "next_node" child.child
  let third:=QueryBranch.bind second "next_slot" (node+48#64)
  let fourth:=QueryBranch.bind third "next_level" (level+prefixLength)
  have rRead : eval source (localVar "node")=some (.val (.word node)):=by simp [eval,evalHOLExact,toExact,localVar,ofString,nodeCell]
  have childRead : eval first (nodeFieldExpression 48#64)=some (.val (.word child.child)):=by
    simp [eval,evalHOLExact,toExact,localVar,nodeFieldExpression,addConst,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      nodeCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
    rw [memLoadHOLExact.eq_1,if_pos child.mapped,child.stored]
  have slotRead : eval second (addConst (localVar "node") 48#64)=some (.val (.word (node+48#64))):=by
    simp [eval,evalHOLExact,toExact,localVar,addConst,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      nodeCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
  have levelRead : eval third (.op .add [localVar "level",localVar "pl"])=some (.val (.word (level+prefixLength))):=by
    simp [eval,evalHOLExact,toExact,localVar,third,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,
      levelCell,prefixCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [extension_descend_shape] at normal
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
  have positive : 0<prefixLength.toNat:=by rw [matched]; exact paths.positive node member active tag
  have addition : (level+prefixLength).toNat=level.toNat+prefixLength.toNat:=BitVec.toNat_add_of_lt (by omega)
  exact ⟨child.child,child.member,Or.inr ⟨node,48,member,active,.extension tag,rfl⟩,addition,
    by rw [addition]; exact before,by rw [addition]; omega,endpoint⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_descend_normal
