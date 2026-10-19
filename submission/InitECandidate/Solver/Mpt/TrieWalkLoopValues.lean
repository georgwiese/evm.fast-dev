import InitECandidate.Solver.Mpt.TrieWalkBodyValues
import InitECandidate.Solver.Mpt.TrieWalkValuesRebase
import InitECandidate.Solver.Mpt.TrieWalkInvariantStep
import InitECandidate.Solver.Input.ReturnFactsLoop

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.ReturnFacts

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem Graph.loop_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property)
    (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (bounded : position.toNat≤limit)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs")=some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    Returns source loop (Answer source.memaddrs valueLimit (property:=property)) := by
  let invariant := Invariant source.memory source.memaddrs source.be graph.valid nibs limit
  have bodyReturns : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → Returns (decClockHOLFinite current) loopBody (Answer source.memaddrs valueLimit (property:=property)) := by
    intro current codeEq valid word observed nonzero clock
    obtain ⟨memoryEq,domainEq,beEq,nibsCurrent,limitCurrent,node,position,member,bounded,nodeCurrent,posCurrent⟩ := valid
    let currentGraph := Graph.rebase source.memory current.memory source.memaddrs current.memaddrs graph memoryEq domainEq
    have currentMember : currentGraph.valid node := by rw [Graph.rebase_valid]; exact member
    have currentValues := Values.rebase source.memory current.memory source.memaddrs current.memaddrs graph valueLimit values memoryEq domainEq
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    have active := condition_active current node word nodeCurrent observed nonzero
    have result := Graph.loop_body_returns (decClockHOLFinite current) currentGraph valueLimit currentValues node currentMember active nodeCurrent currentInstalled
    change Returns (decClockHOLFinite current) loopBody (Answer current.memaddrs valueLimit (property:=property)) at result
    rwa [domainEq] at result
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target result,
      evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(result,target) →
      (result=none ∨ result=some .continue) → invariant target := by
    intro current codeEq valid word observed nonzero clock target result run continuing
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    exact Graph.invariant_step source.memory source.memaddrs source.be graph nibs limit key current target valid currentInstalled word observed nonzero result run continuing
  have valid : invariant source := ⟨rfl,rfl,rfl,nibsCell,limitCell,node,position,member,bounded,nodeCell,posCell⟩
  rw [loop_shape]
  exact Input.ReturnFacts.loop source.code condition loopBody invariant (Answer source.memaddrs valueLimit (property:=property)) bodyReturns progress source rfl valid

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_returns
