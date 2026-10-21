import InitECandidate.Solver.Input.WitnessDecodeSliceEntry
import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.WitnessDecodeControl
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem DecodeSliceEntry.rows (input : Guest.InputBlob)
    (origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit header payload count : BitVec 64) (items : List Rlp.ListItem)
    (entry : DecodeSliceEntry input origin current db pointer length heap cursor limit header payload count items) :
    Mpt.WitnessDecode.Rows current heap (pointer+header) payload.toNat items := by
  have allocation : AllocatedBytes.Arena heap (16*items.length):=by
    rw [←entry.snapshot.countExact]
    exact entry.snapshot.arrayArena
  apply Mpt.WitnessDecode.Rows.of_model current heap (pointer+header) payload.toNat items entry.snapshot.arena.domain entry.snapshot.itemModel entry.snapshot.records allocation entry.snapshot.arrayAligned
  rw [entry.pointerNumber]
  have extent:=entry.extent
  have before:=entry.inputBeforeHeap
  have upper:=heap.isLt
  omega

theorem DecodeSliceEntry.bind_array (input : Guest.InputBlob)
    (origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit header payload count : BitVec 64) (items : List Rlp.ListItem)
    (entry : DecodeSliceEntry input origin current db pointer length heap cursor limit header payload count items) :
    DecodeSliceEntry input origin (bind current "arr" heap) db pointer length heap cursor limit header payload count items := by
  have physical:=entry.snapshot.of_erase _ current (bind current "arr" heap) (pointer+header) payload heap cursor limit count items rfl
  have retained (name : String) (different : ofString "arr"≠ofString name) :
      (bind current "arr" heap).locals.lookup (ofString name)=current.locals.lookup (ofString name):=
    bind_lookup_other current "arr" name heap different
  have boundary:=entry.boundary.erase_frame input current (bind current "arr" heap) rfl (retained "db" (by decide))
  exact ⟨entry.complete,entry.extent,entry.pointerNumber,entry.sourceHeap,entry.inputBeforeHeap,entry.inputBeforeDb,entry.inputLower,entry.lengthBound,
    physical,boundary,entry.installed,(retained "db" (by decide)).trans entry.dbCell,(retained "p" (by decide)).trans entry.pointerCell,
    (retained "n" (by decide)).trans entry.lengthCell,(retained "it" (by decide)).trans entry.itemCell,(retained "sl" (by decide)).trans entry.sliceCell⟩

/-- The real typed sl pair executes the original arr declaration on every
outcome. Its current physical context survives at the exact real suffix. -/
theorem DecodeSliceEntry.array_trace (input : Guest.InputBlob)
    (origin current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit header payload count : BitVec 64) (items : List Rlp.ListItem)
    (entry : DecodeSliceEntry input origin current db pointer length heap cursor limit header payload count items)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState current Mpt.WitnessDecode.afterSlices=(outcome,post)) :
    ∃ inner,evaluateHOLFiniteState (bind current "arr" heap) Mpt.WitnessDecode.afterArray=(outcome,inner) ∧ post=restore current "arr" inner := by
  have read : eval current (Mpt.WitnessDecode.field "sl" 0)=some (.val (.word heap)):=by
    simp [eval,Mpt.WitnessDecode.field,evalHOLExact,localVar,toExact,entry.sliceCell,Rlp.Slices.result]
  have shape : Mpt.WitnessDecode.afterSlices=.dec (ofString "arr") .one (Mpt.WitnessDecode.field "sl" 0) Mpt.WitnessDecode.afterArray:=by
    rw [Mpt.WitnessDecode.after_slices_shape,Mpt.WitnessDecode.after_array_shape]
  rw [shape] at run
  exact ScalarScope.declare_trace current post "arr" _ heap Mpt.WitnessDecode.afterArray outcome read run

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.DecodeSliceEntry.rows
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.DecodeSliceEntry.bind_array
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.DecodeSliceEntry.array_trace
