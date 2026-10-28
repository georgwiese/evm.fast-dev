import InitECandidate.Solver.Input.CurrentVerify.DatabaseContext
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.ReturnedFrame
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.EntryUpper

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- An actual database return protects every earlier object up to the
incoming heap, including a previously constructed Patricia database. -/
theorem database_returned {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (limitBound : limit≤65536) (small : VarList.decodedCount input start length<2^31)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentTable.NodeBuild.body=(some (.returned value),post)) :
    ∃ table cap upper,value=.val (.word table) ∧ boundary≤upper ∧
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 upper))) ∧
      CurrentTable.NodeBuild.Returned {databaseData input array pointer start length boundary limit with upper:=upper} source post table cap := by
  have initial := database_entry data image limitBound small callee arrayCell countCell
  obtain ⟨heap,heapCell,lower,upper,aligned⟩ := data.heap
  have heapAtLeast : NormalHeapEffects.AtLeast heap.toNat (callEntryStateHOLFinite source callee) :=
    ⟨heap,heapCell,Nat.le_refl _,upper,aligned⟩
  have raised := initial.raise_upper heap.toNat (by change boundary≤heap.toNat; omega) heapAtLeast
  obtain ⟨table,cap,answer,result⟩ := CurrentTable.NodeBuild.body_returned _ _ _ raised value run
  refine ⟨table,cap,heap.toNat,answer,by omega,?_,result.of_frames rfl rfl⟩
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using heapCell

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_returned
