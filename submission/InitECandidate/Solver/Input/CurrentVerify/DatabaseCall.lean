import InitECandidate.Solver.Input.CurrentVerify.DatabaseData
import InitECandidate.Solver.Input.CurrentVerify.DatabaseCost
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Either actual database caller stops within its uniform source allowance,
or resumes its original continuation with the genuine table, all decoded
inputs and a frame protecting the entire earlier persistent heap. -/
theorem database_call_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (limitBound : limit≤65536) (small : VarList.decodedCount input start length<2^31)
    (name : String) (different : ofString name≠ofString "si")
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") arguments continuation)=(outcome,post)) :
    source.clock-post.clock≤1661620382 ∨ ∃ current inner table cap upper,
      Data input current pointer si record gasWord boundary ∧ boundary≤upper ∧
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 upper))) ∧
      CurrentTable.NodeBuild.Returned {databaseData input array pointer start length boundary limit with upper:=upper} source current table cap ∧
      current.locals.lookup (ofString name)=some (.val (.word table)) ∧
      (∀ key : MlS,ofString name≠key → current.locals.lookup key=source.locals.lookup key) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1661620382 ∧
      evaluateHOLFiniteState current continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := word_pair_environment source.code.lookup (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
    CurrentTable.NodeBuild.body .one (VarList.decodedArray array length) (BitVec.ofNat 64 (VarList.decodedCount input start length)) (by decide)
    (CurrentTable.NodeBuild.original_code source.code data.arena.code)
  have price := database_uniform_body_cost data image limitBound small callee arrayCell countCell
    (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentTable.NodeBuild.body).1 rfl
  rcases CallNormal.scoped_trace source post name .one (ofString "nodedb_build") arguments _ CurrentTable.NodeBuild.body continuation callee .one
    1661620381 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨table,cap,upper,answer,upperBound,heapCell,result⟩ := database_returned data image limitBound small callee arrayCell countCell value bodyRun
    rw [answer] at continued
    let current := CallNormal.continuationEntry source target name (.val (.word table))
    have next := after_database_data data name different upperBound result
    have physical : CurrentTable.NodeBuild.Returned {databaseData input array pointer start length boundary limit with upper:=upper} source current table cap := result.of_frames rfl rfl
    have others (key : MlS) (other : ofString name≠key) : current.locals.lookup key=source.locals.lookup key := by
      simp [current,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other]
    exact Or.inr ⟨current,inner,table,cap,upper,next,upperBound,heapCell,physical,CallNormal.continuation_lookup_same source target name _,others,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_call_trace
