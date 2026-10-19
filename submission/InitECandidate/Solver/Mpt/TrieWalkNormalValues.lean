import InitECandidate.Solver.Mpt.TrieWalkLoopValues
import InitECandidate.Solver.Mpt.TrieWalkCost

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem Graph.body_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property)
    (node nibs : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs")=some (.val (.word nibs)))
    (limitCell : source.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    Returns source body (Answer source.memaddrs valueLimit (property:=property)) := by
  rw [body_shape]
  refine Input.ReturnFacts.declared_word source "pos" (.const 0#64) 0#64 (.seq loop afterLoop)
    (Answer source.memaddrs valueLimit (property:=property)) rfl ?_
  let entered := bind source "pos" 0#64
  have currentNode : entered.locals.lookup (ofString "node")=some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs")=some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentLimit : entered.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have currentPos : entered.locals.lookup (ofString "pos")=some (.val (.word 0#64)) := bind_lookup_same _ _ _
  apply Input.ReturnFacts.sequence
  · exact Graph.loop_returns entered graph valueLimit values node nibs 0#64 limit key member (by simp) currentNode currentNibs currentPos currentLimit installed
  · intro middle normal
    rw [after_loop_shape]
    exact absent_returns middle source.memaddrs valueLimit

/-- Complete actual normal original walk: binary flag, real bounded mapped
payload on hits, nonlocal read-only frame and its consumed source clocks.
There is no supplied helper execution or funding premise. -/
theorem Graph.body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property)
    (node nibs : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs")=some (.val (.word nibs)))
    (limitCell : source.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),target)) :
    Answer target.memaddrs valueLimit (property:=property) returned ∧ target.clock≤source.clock ∧ source.clock-2080≤target.clock ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have answer := Graph.body_returns source graph valueLimit values node nibs limit key member nodeCell nibsCell limitCell installed target returned normal
  have cost := Graph.body_cost source graph node nibs limit key member nodeCell nibsCell limitCell installed
  have clock := evaluateHOLFiniteState_clock_le source body
  have fields := readonly source.code installed source rfl
  rw [normal] at cost clock fields
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  change target.memaddrs=source.memaddrs at domain
  exact ⟨by rwa [domain],clock,by change source.clock-target.clock≤2080 at cost; omega,fields⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.body_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.body_normal
