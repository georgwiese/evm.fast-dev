import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyReturned
import InitECandidate.Solver.MutableTable.WitnessDatabaseFields
import InitECandidate.Solver.MutableTable.NodeDbEnvironment
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Every original database scope is bounded before returning, or reaches
its genuine checked continuation. Arbitrary query memory is included; full
nonlocal preservation follows from the original bodies on every outcome. -/
theorem Database.any_scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch query : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (NodeDb.arguments table query))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) NodeDb.resultShape (ofString "nodedb_lookup") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤6*count+4 ∨ ∃ target answer inner,
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ target.clock≤source.clock ∧ source.clock-target.clock≤6*count+4 ∧
      (∀ slice,answer=some slice→∃ index<count,slice=slices index ∧ slice.2.toNat≤maximum ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat) ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (NodeDb.output answer)) continuation=(outcome,inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,dbCell,hashCell⟩ := NodeDb.environment source.code.lookup table query (NodeDb.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have data:=actual.of_fields source entry array table count maximum slices scratch rfl rfl rfl
  have price:=data.any_body_cost entry array table count maximum slices scratch query installed dbCell hashCell
  rcases Input.CallNormal.scoped_trace source post name NodeDb.resultShape (ofString "nodedb_lookup") expressions _ NodeDb.body continuation callee NodeDb.resultShape (6*count+3)
      args called price outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩ := reached
    obtain ⟨answer,valueEq,pure,bodySpent,hit⟩ := data.any_body_returned entry target array table count maximum slices scratch query installed dbCell hashCell returned bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,answer,inner,pure,forward,by omega,hit,continued,endpoint⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.any_scoped_trace
