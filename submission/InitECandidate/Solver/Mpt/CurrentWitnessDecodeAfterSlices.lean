import InitECandidate.Solver.Mpt.CurrentWitnessDecodeAfterArray
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem after_slices_array_shape : afterSlices=.dec (ofString "arr") .one (field "sl" 0) afterArray := by
  rw [after_slices_shape,after_array_shape]

theorem slices_array_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count)) :
    eval source (field "sl" 0)=some (.val (.word array)) := by
  simp [eval,field,localVar,toExact,evalHOLExact,sliceCell,Rlp.Slices.result]

/-- Extracting the array from the actual converter result preserves its
physical records and all input/allocator obligations. -/
theorem current_after_slices_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap count : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤bytes/4+120*bytes+266 := by
  rw [after_slices_array_shape]
  exact ClockCost.declared_current source "arr" (field "sl" 0) array afterArray _ (slices_array_read source array count sliceCell)
    (current_after_array_price (bind source "arr" array) array pointer heap count bytes items
      (rows.frame source _ array pointer bytes items rfl (by intros; rfl)) countEq
      ((bind_lookup_other source "arr" "sl" array (by decide)).trans sliceCell) (bind_lookup_same _ _ _)
      small beforeArray heapCell heapArena heapBound aligned (arena.of_frame rfl))

theorem current_after_slices_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source afterSlices BinaryResult := by
  rw [after_slices_array_shape]
  apply ReturnFacts.declared
  intro value
  exact current_after_array_binary _

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_slices_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_slices_binary
