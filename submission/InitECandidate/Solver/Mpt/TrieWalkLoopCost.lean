import InitECandidate.Solver.Mpt.TrieWalkInvariant
import InitECandidate.Solver.Mpt.TrieWalkBodyNormal
import InitECandidate.Solver.Mpt.TrieWalkBodyCost
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An instantiated bound for the original trie loop, conditional on a
current physical closed graph and valid key buffer. This does not establish
that main's startup/decoding/mutations produce those entry conditions. -/
theorem Graph.loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 16 * currentRank limit source := by
  let invariant := Invariant source.memory source.memaddrs source.be graph.valid nibs limit
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition = some (.val (.word word)) →
      word ≠ 0#64 → current.clock ≠ 0 →
      current.clock - 1 - (evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2.clock ≤ 15 := by
    intro current codeEq valid word observed nonzero clock
    obtain ⟨memoryEq, domainEq, beEq, nibsCurrent, limitCurrent, node, position, member, bounded, nodeCurrent, posCurrent⟩ := valid
    let currentGraph := Graph.rebase source.memory current.memory source.memaddrs current.memaddrs graph memoryEq domainEq
    have currentMember : currentGraph.valid node := by
      rw [Graph.rebase_valid]
      exact member
    have currentKey : KeyView current.memory current.memaddrs current.be nibs limit := by
      rw [memoryEq, domainEq, beEq]
      exact key
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    have active := condition_active current node word nodeCurrent observed nonzero
    exact Graph.loop_body_cost (decClockHOLFinite current) currentGraph node nibs position limit currentKey
      currentMember active bounded nodeCurrent nibsCurrent posCurrent limitCurrent currentInstalled
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition = some (.val (.word word)) →
      word ≠ 0#64 → 0 < currentRank limit current ∧
        (current.clock ≠ 0 →
          let output := evaluateHOLFiniteState (decClockHOLFinite current) loopBody
          (output.1 = none ∨ output.1 = some .continue) → invariant output.2 ∧ currentRank limit output.2 < currentRank limit current) := by
    intro current codeEq valid word observed nonzero
    obtain ⟨memoryEq, domainEq, beEq, nibsCurrent, limitCurrent, node, position, member, bounded, nodeCurrent, posCurrent⟩ := valid
    let currentGraph := Graph.rebase source.memory current.memory source.memaddrs current.memaddrs graph memoryEq domainEq
    have currentMember : currentGraph.valid node := by
      rw [Graph.rebase_valid]
      exact member
    have currentKey : KeyView current.memory current.memaddrs current.be nibs limit := by
      rw [memoryEq, domainEq, beEq]
      exact key
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    have active := condition_active current node word nodeCurrent observed nonzero
    constructor
    · rw [current_rank_eq current node position limit nodeCurrent posCurrent]
      exact Rank.positive limit current.memory node position active
    · intro clock
      let entry := decClockHOLFinite current
      let output := evaluateHOLFiniteState entry loopBody
      change (output.1 = none ∨ output.1 = some .continue) →
        invariant output.2 ∧ currentRank limit output.2 < currentRank limit current
      intro continuing
      have normalResult : output.1 = none := continuing.resolve_right (loop_body_no_continue entry)
      have run : evaluateHOLFiniteState entry loopBody = (none, output.2) := Prod.ext normalResult rfl
      obtain ⟨nextNode, nextPosition, nextMember, nextBounded, nextNodeCell, nextPosCell, smaller⟩ :=
        Graph.loop_body_normal entry output.2 currentGraph node nibs position limit currentKey currentMember active bounded
          nodeCurrent nibsCurrent posCurrent limitCurrent currentInstalled run
      have fields := loop_body_readonly current.code currentInstalled entry rfl
      rw [run] at fields
      have nextMemory := congrArg PanSemStateFiniteExact.memory fields
      have nextDomain := congrArg PanSemStateFiniteExact.memaddrs fields
      have nextBe := congrArg PanSemStateFiniteExact.be fields
      change output.2.memory = current.memory at nextMemory
      change output.2.memaddrs = current.memaddrs at nextDomain
      change output.2.be = current.be at nextBe
      have constants := loop_body_constants entry output.2 run
      constructor
      · refine ⟨nextMemory.trans memoryEq, nextDomain.trans domainEq, nextBe.trans beEq,
          constants.2.trans nibsCurrent, constants.1.trans limitCurrent, nextNode, nextPosition, ?_, nextBounded, nextNodeCell, nextPosCell⟩
        rw [Graph.rebase_valid] at nextMember
        exact nextMember
      · rw [current_rank_eq output.2 nextNode nextPosition limit nextNodeCell nextPosCell,
          current_rank_eq current node position limit nodeCurrent posCurrent]
        exact smaller
  have valid : invariant source := ⟨rfl, rfl, rfl, nibsCell, limitCell, node, position, member, bounded, nodeCell, posCell⟩
  rw [loop_shape]
  exact Input.ClockCost.ranked_loop_current source.code condition loopBody 15 invariant (currentRank limit)
    priced progress source rfl valid

theorem Graph.loop_cost_2080 (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 2080 := by
  have cost := Graph.loop_cost source graph node nibs position limit key member bounded nodeCell nibsCell posCell limitCell installed
  have rank := current_rank_upper source limit
  have small := key.small
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_cost
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_cost_2080
