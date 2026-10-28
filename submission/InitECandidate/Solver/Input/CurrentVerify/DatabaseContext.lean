import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.CurrentStartup.WitnessRows
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.BodyCost

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The same builder handles both original decoded node and code arrays. -/
def databaseData (input : Guest.InputBlob) (array pointer : BitVec 64) (start length boundary limit : Nat) : CurrentTable.NodeBuild.Data :=
  {array:=VarList.decodedArray array length,table:=0#64,cap:=0#64,out:=2701134768#64,
   stp:=2701132160#64,pad:=2701132360#64,pointers:=VarList.recordPointer input pointer start,
   lengths:=VarList.recordLength input start length (VarList.decodedCount input start length),
   total:=VarList.decodedCount input start length,lower:=2701134824,upper:=boundary,itemLimit:=limit}

/-- The actual decoded array, retained MPT pointer and current heap derive
all whole-builder entry conditions at its real callee. No successful future
allocation, hash or insertion is supplied. -/
theorem database_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (limitBound : limit≤65536) (small : VarList.decodedCount input start length<2^31)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length))))) :
    CurrentTable.NodeBuild.Entry (databaseData input array pointer start length boundary limit) (callEntryStateHOLFinite source callee) := by
  let entry := callEntryStateHOLFinite source callee
  have rows := image.rows data.arena.domain (by omega)
  have entryRows := rows.of_frame source entry _ _ _ _ _ _ ⟨by intro query lower upper; rfl⟩
  obtain ⟨heap,cell,lower,upper,aligned⟩ := data.heap
  have workspace : CurrentTable.Workspace entry boundary 2701132160#64 2701132360#64 :=
    ⟨data.arena.of_frame rfl,data.keccak.of_frame rfl,⟨heap,cell,by omega,upper,aligned⟩,
      by have := data.recordInside; omega⟩
  exact ⟨workspace,data.little,entryRows,data.mptHash,arrayCell,countCell,small,
    (by change 2701132160+200≤2701134824; decide),
    (by change 2701132360+136≤2701134824; decide),
    (by change 2701134768+32≤2701134824; decide),
    (show AllocatedBytes.Arena 2701134768#64 32 from ⟨by decide,by decide⟩),
    (by change 2701134768%8=0; decide),
    (by change 2701134824≤boundary; have := data.recordInside; omega),
    (by change 2701134824<2^64; decide),image.lengths,
    (by change limit+136<2^64; omega)⟩

/-- The actual record-size budget, not a separate per-item maximum,
supplies the aggregate byte allowance for this very decoded builder. -/
theorem database_body_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (limitBound : limit≤65536) (small : VarList.decodedCount input start length<2^31)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentTable.NodeBuild.body=(outcome,post)) :
    (callEntryStateHOLFinite source callee).clock-post.clock≤44*(length/136)+1507*VarList.decodedCount input start length+36 := by
  have entry := database_entry data image limitBound small callee arrayCell countCell
  have budget := image.records.size_bounds source input pointer array start length
  exact CurrentTable.NodeBuild.body_byte_cost _ _ _ entry length budget.1 outcome run

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.database_body_cost
