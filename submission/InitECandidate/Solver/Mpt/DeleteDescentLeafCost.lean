import InitECandidate.Solver.Mpt.DeleteDescentLeafNormal
import InitECandidate.Solver.MutableTable.MemeqSmallCallCost

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem leaf_compared_price (code) : Input.ClockCost.Bound code leafCompared 0 := by
  rw [leaf_shapes.2.2.2]
  exact Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.skip code)

/-- Genuine mapped operands yield the original small-comparison price
for every outcome, rather than multiplying a generic byte-loop cap. -/
theorem leaf_compare_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) (matched : wordAt source.memory (model.node+40#64)=length-model.level) :
    source.clock-(evaluateHOLFiniteState source leafCompare).2.clock≤15 := by
  have left:=model.pending.paths.span model.node model.nodeMember active (Or.inl tag)
  rw [matched] at left
  have right:=descent_query_suffix source key length limit nodeLower pathLower property model
  have number:=descent_remaining_number source key length limit nodeLower pathLower property model
  have small : (length-model.level).toNat≤64:=by have bounded:=model.bounded; omega
  have args:=leaf_compare_arguments source key length limit nodeLower pathLower property model active tag
  rw [leaf_shapes.2.2.1]
  have priced:=MutableTable.MemeqSmall.call_cost source (wordAt source.memory (model.node+32#64)) (key+model.level) (length-model.level).toNat
    small left.fits right.span.fits left.mapped right.span.mapped (MutableTable.MemeqAny.original_code source.code model.pending.installed)
    (ofString "eq") leafCompareArguments leafCompared args (leaf_compared_price source.code)
  have maximum : MutableTable.MemeqByteRuntime.price (length-model.level).toNat+1≤15:=by
    unfold MutableTable.MemeqByteRuntime.price
    omega
  exact priced.trans maximum

theorem leaf_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) :
    source.clock-(evaluateHOLFiniteState source leafLengthChoice).2.clock≤15 := by
  rw [leaf_length_dispatch source key length limit nodeLower pathLower property model active tag]
  by_cases matched : wordAt source.memory (model.node+40#64)=length-model.level
  · rw [if_pos matched]
    exact leaf_compare_cost source key length limit nodeLower pathLower property model active tag matched
  · rw [if_neg matched]
    change source.clock-source.clock≤15
    omega

/-- Every outcome of the original terminal leaf body costs at most15
source call/loop ticks, including comparison failure and timeout. -/
theorem leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) :
    source.clock-(evaluateHOLFiniteState source leafBlock).2.clock≤15 := by
  have nodeRead : eval source (localVar "node")=some (.val (.word model.node)):=by simp [eval,localVar,evalHOLExact,toExact,model.nodeCell]
  have assigned:=assign_result_execute source key length limit nodeLower pathLower property model (localVar "node") model.node nodeRead
  let selectedState:=QueryBranch.bind source "res" model.node
  let selected:=model.bind_result source key length limit nodeLower pathLower property model.node model.nodeMember
  rw [leaf_shapes.1,StateSteps.next_sequence source selectedState _ leafLengthChoice assigned (Nat.le_refl _)]
  exact leaf_length_cost selectedState key length limit nodeLower pathLower property selected active tag

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_compared_price
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_compare_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_length_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_cost
