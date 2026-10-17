import InitECandidate.Solver.MutableTable.WitnessBuildKeyHistory
import InitECandidate.Solver.MutableTable.WitnessDictionaryLookup
import InitECandidate.Solver.WitnessRadix.OrdinalArray
import InitECandidate.Solver.WitnessRadix.OrdinalTree

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open WitnessRadix WitnessRadix.BackingLayout
attribute [local instance] Classical.propDecidable

/-- The original history's decoded slices are exactly the radix builder's
ordinal entries once their observed keys have been synchronized. -/
theorem sliceEntries_keysMatch (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (input : List (Find.Key32 × BitVec 64)) (matching : KeysMatch plan keyFor input)
    (length : input.length ≤ plan.count) :
    sliceEntries plan (fun i => sliceFor (BitVec.ofNat 64 i)) input =
      OrdinalTree.entries keyFor sliceFor (ordinals input.length) := by
  change input.map _ = _
  calc
    input.map _ = (keyRecords plan keyFor input.length).map _ := congrArg (List.map _) matching
    _ = _ := by
      unfold keyRecords OrdinalTree.entries ordinals
      simp only [List.map_map]
      apply List.map_congr_left
      intro index member
      have inside : index < plan.count := by have := List.mem_range.mp member; omega
      simp only [Function.comp_apply]
      rw [recordSlices_address plan ready (fun i => sliceFor (BitVec.ofNat 64 i)) index inside]

theorem dictionary_last_agrees (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (input : List (Find.Key32 × BitVec 64)) (matching : KeysMatch plan keyFor input)
    (length : input.length ≤ plan.count) (query : ByteKeys.Key) :
    lastValue query (sliceEntries plan (fun i => sliceFor (BitVec.ofNat 64 i)) input) =
      lastValue query (OrdinalTree.entries keyFor sliceFor (ordinals input.length)) := by
  rw [sliceEntries_keysMatch plan ready keyFor sliceFor input matching length]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.sliceEntries_keysMatch
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.dictionary_last_agrees
