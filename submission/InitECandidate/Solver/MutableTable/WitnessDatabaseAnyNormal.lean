import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyReturned
import InitECandidate.Solver.MutableTable.WitnessDatabaseFields
import InitECandidate.Solver.MutableTable.NodeDbEnvironment
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine returning original lookup scope reaches its actual
continuation with either absence or one of the bounded constructed slices.
This normal-return contract does not use a stopping-cost alternative. -/
theorem Database.any_scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch query : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (NodeDb.arguments table query))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) NodeDb.resultShape (ofString "nodedb_lookup") expressions continuation)=(some (.returned value),post)) :
    ∃ target answer inner,
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧
      (∀ slice,answer=some slice→∃ index<count,slice=slices index ∧ slice.2.toNat≤maximum ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat) ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (NodeDb.output answer)) continuation=(some (.returned value),inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,dbCell,hashCell⟩:=NodeDb.environment source.code.lookup table query (NodeDb.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have data:=actual.of_fields source entry array table count maximum slices scratch rfl rfl rfl
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name NodeDb.resultShape
    (ofString "nodedb_lookup") expressions _ NodeDb.body continuation callee NodeDb.resultShape args called value normal
  obtain ⟨answer,valueEq,pure,bodySpent,hit⟩:=data.any_body_returned entry target array table count maximum slices scratch query installed dbCell hashCell returned bodyRun
  rw [valueEq] at continued
  exact ⟨target,answer,inner,pure,hit,continued,endpoint⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.any_scoped_normal
