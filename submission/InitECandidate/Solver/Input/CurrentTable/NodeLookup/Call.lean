import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Returned
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Cost
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The original three-word database lookup caller either stops within265ticks or
resumes with the genuine absent/decoded-record result and full physical frame. -/
theorem scoped_trace (data : NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys (NodeBuild.ValueOf data))
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (installed : OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "nodedb_lookup") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤265 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target value inner,
      Result data value ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤265 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩ := word_pair_environment source.code.lookup (ofString "nodedb_lookup") (ofString "db") (ofString "hash")
    body resultShape table pointer (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have entryImage : Image entry table cap root next count valid bits left right keys (NodeBuild.ValueOf data) := image.of_frame rfl
  have entryRows := rows.of_frame source entry data.array data.pointers data.lengths data.total data.lower data.upper ⟨by intro query lower upper; rfl⟩
  have price := body_cost entry table cap root pointer next count valid bits left right keys (NodeBuild.ValueOf data)
    entryImage tableCell keyCell installed
  rcases CallNormal.scoped_classified source post name resultShape (ofString "nodedb_lookup") expressions _ body continuation callee resultShape
    264 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨result,frame⟩ := body_returned data entry target table cap root pointer next count valid bits left right keys entryImage entryRows tableCell keyCell installed value bodyRun
    exact Or.inr ⟨target,value,inner,result,frame,forward,cost,continued,endpoint⟩

theorem scoped_returned (data : NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys (NodeBuild.ValueOf data))
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (installed : OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word table),.val (.word pointer)]) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "nodedb_lookup") expressions continuation)=(some (.returned returned),post)) :
    ∃ target value inner,Result data value ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤265 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  rcases scoped_trace data source post table cap root pointer next count valid bits left right keys image rows installed name expressions continuation args
    (some (.returned returned)) run with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.scoped_returned
