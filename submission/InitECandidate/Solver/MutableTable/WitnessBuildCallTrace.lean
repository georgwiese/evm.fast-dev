import InitECandidate.Solver.MutableTable.WitnessBuildCallee
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.ScopedCallSuccess

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) extends Normal source target array heap count stp pad scratch where
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤bodyPrice slices count+1

/-- Every real original constructor scope, including the unmapped empty
sentinel branch, stops within its allowance or resumes its genuine caller
with the actual allocated table and complete normal output/frame. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (values array count))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤bodyPrice slices count+1 ∨ ∃ target inner,Returned source target array heap count slices stp pad scratch ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (.val (.word heap))) continuation=(outcome,inner) ∧ post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := environment source.code.lookup array count (original_code source.code actual.installed)
  have price:=callee_cost source array heap count maximum slices stp pad scratch actual callee arrayCell countCell
  rcases Input.CallNormal.scoped_trace source post name .one (ofString "nodedb_build") expressions _ body continuation callee .one (bodyPrice slices count) args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨valueEq,summary⟩ := callee_normal source target array heap count maximum slices stp pad scratch actual callee arrayCell countCell value bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,inner,⟨summary,forward,cost⟩,continued,endpoint⟩

/-- A real successful enclosing scope forces the original constructor's
normal table return; all data and clock funding follow from that execution. -/
theorem scoped_success (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (values array count))
    (outcome : Option (PanSemResultExact 64)) (success : outcome=none ∨ ∃ value,outcome=some (.returned value))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") expressions continuation)=(outcome,post)) :
    ∃ target inner,Returned source target array heap count slices stp pad scratch ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (.val (.word heap))) continuation=(outcome,inner) ∧ post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := environment source.code.lookup array count (original_code source.code actual.installed)
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_success source post name .one (ofString "nodedb_build") expressions _ body continuation callee .one args called outcome success run
  obtain ⟨valueEq,summary⟩ := callee_normal source target array heap count maximum slices stp pad scratch actual callee arrayCell countCell value bodyRun
  have price:=callee_cost source array heap count maximum slices stp pad scratch actual callee arrayCell countCell
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤bodyPrice slices count at price
  change target.clock≤source.clock-1 at forward
  rw [valueEq] at continued
  exact ⟨target,inner,⟨summary,by omega,by omega⟩,continued,endpoint⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.scoped_trace
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.scoped_success
