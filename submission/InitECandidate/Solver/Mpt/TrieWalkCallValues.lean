import InitECandidate.Solver.Mpt.TrieWalkNormalValues
import InitECandidate.Solver.Mpt.TrieWalkCall
import InitECandidate.Solver.Input.TailCallNormal

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
/-- The real original trie_walk tail call exposes its actual binary/payload
answer and read-only frame, with at most2081source clocks. -/
theorem Graph.tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (nodeValues : Values graph valueLimit)
    (node nibs : BitVec 64) (length : Nat) (key : KeyView source.memory source.memaddrs source.be nibs length)
    (member : graph.valid node) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values node nibs length))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call none (ofString "trie_walk") arguments)=(some (.returned returned),post)) :
    1≤source.clock ∧ Answer post.memaddrs valueLimit returned ∧ post.clock≤source.clock-1 ∧
      source.clock-2081≤post.clock ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  obtain ⟨callee,called,nodeLocal,nibsLocal,lengthLocal⟩ := environment source.code.lookup node nibs length (original_code source.code installed)
  obtain ⟨positive,target,bodyRun,checked,postEq⟩ := Input.CallNormal.tail_callee_return source post (ofString "trie_walk") arguments _ body callee resultShape args called returned normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨answer,upper,lower,fields⟩ := Graph.body_normal entry target graph valueLimit nodeValues node nibs length key member nodeLocal nibsLocal lengthLocal installed returned bodyRun
  rw [postEq]
  change target.clock≤source.clock-1 at upper
  change source.clock-1-2080≤target.clock at lower
  exact ⟨positive,answer,upper,by change source.clock-2081≤target.clock; omega,fields⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.tail_normal
