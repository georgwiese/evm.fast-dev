import InitECandidate.Solver.Input.CurrentVerify.DatabaseContext
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Call

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A found database value is an actual bounded decoded input slice. -/
def LookupResult (input : Guest.InputBlob) (pointer : BitVec 64)
    (start length boundary limit : Nat) (value : ValueHOL 64) : Prop :=
  value=CurrentTable.NodeLookup.absentValue ∨
  ∃ index<VarList.decodedCount input start length,
    let p:=VarList.recordPointer input pointer start index
    let n:=VarList.recordLength input start length (VarList.decodedCount input start length) index
    value=CurrentTable.NodeLookup.presentValue p n ∧
    AllocatedBytes.Arena p n.toNat ∧ 2701134824≤p.toNat ∧ p.toNat+n.toNat≤boundary ∧ n.toNat≤limit

/-- The actual current lookup caller derives a bounded witness slice from
its matching physical table and decoded-array image. No successful lookup,
query bytes, or later decode outcome is assumed. -/
theorem database_lookup_trace_image {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap query : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (installed : OriginalCode.Installed source.code)
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary limit with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (sizeBound : 16*limit<2^64) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word table),.val (.word query)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) CurrentTable.NodeLookup.resultShape
      (ofString "nodedb_lookup") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤265 ∧ ∀ value,outcome≠some (.returned value)) ∨
    ∃ target value inner,
      LookupResult input pointer start length boundary limit value ∧
      LocalEffects.erase target=LocalEffects.erase source ∧ target.clock≤source.clock ∧ source.clock-target.clock≤265 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  let data:=databaseData input array pointer start length boundary limit
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,countBound⟩ := tableImage
  have rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper :=
    witness.rows image.domain sizeBound
  have currentImage : CurrentTable.Image source table cap root next count valid bits left right keys (CurrentTable.NodeBuild.ValueOf data) := image
  rcases CurrentTable.NodeLookup.scoped_trace data source post table cap root query next count valid bits left right keys
    currentImage rows installed name expressions continuation args outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,result,frame,forward,cost,continued,endpoint⟩ := reached
    refine Or.inr ⟨target,value,inner,?_,frame,forward,cost,continued,endpoint⟩
    rcases result with absent|⟨index,inside,present⟩
    · exact Or.inl absent
    · exact Or.inr ⟨index,inside,present,rows.inputArena index inside,rows.inputAfter index inside,
        rows.inputBefore index inside,witness.lengths index inside⟩

/-- A completed actual builder supplies the minimal lookup image directly. -/
theorem database_lookup_trace {input : Guest.InputBlob}
    {source origin post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap query : BitVec 64} {start length boundary offset limit countLimit upper : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (tableResult : CurrentTable.NodeBuild.Returned
      {databaseData input array pointer start length boundary limit with upper:=upper} origin source table cap)
    (sizeBound : 16*limit<2^64) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word table),.val (.word query)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) CurrentTable.NodeLookup.resultShape
      (ofString "nodedb_lookup") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤265 ∧ ∀ value,outcome≠some (.returned value)) ∨
    ∃ target value inner,
      LookupResult input pointer start length boundary limit value ∧
      LocalEffects.erase target=LocalEffects.erase source ∧ target.clock≤source.clock ∧ source.clock-target.clock≤265 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(outcome,inner) ∧
      post=restore source name inner :=
  database_lookup_trace_image witness tableResult.arena.code tableResult.image sizeBound name expressions continuation args outcome run

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_lookup_trace

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_lookup_trace_image
