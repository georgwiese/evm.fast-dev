import InitECandidate.Solver.Mpt.TrieWalkInvariant
import InitECandidate.Solver.Mpt.TrieWalkBodyNormal
import InitECandidate.Solver.Mpt.TrieWalkControl

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix.QueryBranch

/-- Preserve the physical walk invariant through the actual continuing body.
This separates invariant construction from either loop pricing or returns. -/
theorem Graph.invariant_step (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool)
    (graph : Graph memory domain) (nibs : BitVec 64) (limit : Nat) (key : KeyView memory domain be nibs limit)
    (current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : Invariant memory domain be graph.valid nibs limit current)
    (installed : Input.OriginalCode.Installed current.code) (word : BitVec 64)
    (observed : evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)))
    (nonzero : word≠0#64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(result,target))
    (continuing : result=none ∨ result=some .continue) : Invariant memory domain be graph.valid nibs limit target := by
  obtain ⟨memoryEq,domainEq,beEq,nibsCurrent,limitCurrent,node,position,member,bounded,nodeCurrent,posCurrent⟩ := valid
  let currentGraph := Graph.rebase memory current.memory domain current.memaddrs graph memoryEq domainEq
  have currentMember : currentGraph.valid node := by rw [Graph.rebase_valid]; exact member
  have currentKey : KeyView current.memory current.memaddrs current.be nibs limit := by rw [memoryEq,domainEq,beEq]; exact key
  have active := condition_active current node word nodeCurrent observed nonzero
  let entry := decClockHOLFinite current
  have entryRun : evaluateHOLFiniteState entry loopBody=(result,target) := run
  have noContinue := loop_body_no_continue entry
  rw [entryRun] at noContinue
  have normalResult : result=none := continuing.resolve_right noContinue
  rw [normalResult] at run
  obtain ⟨nextNode,nextPosition,nextMember,nextBounded,nextNodeCell,nextPosCell,smaller⟩ :=
    Graph.loop_body_normal entry target currentGraph node nibs position limit currentKey currentMember active bounded
      nodeCurrent nibsCurrent posCurrent limitCurrent installed run
  have fields := loop_body_readonly current.code installed entry rfl
  rw [run] at fields
  have nextMemory := congrArg PanSemStateFiniteExact.memory fields
  have nextDomain := congrArg PanSemStateFiniteExact.memaddrs fields
  have nextBe := congrArg PanSemStateFiniteExact.be fields
  change target.memory=current.memory at nextMemory
  change target.memaddrs=current.memaddrs at nextDomain
  change target.be=current.be at nextBe
  have constants := loop_body_constants entry target run
  refine ⟨nextMemory.trans memoryEq,nextDomain.trans domainEq,nextBe.trans beEq,
    constants.2.trans nibsCurrent,constants.1.trans limitCurrent,nextNode,nextPosition,?_,nextBounded,nextNodeCell,nextPosCell⟩
  rw [Graph.rebase_valid] at nextMember
  exact nextMember

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.invariant_step
