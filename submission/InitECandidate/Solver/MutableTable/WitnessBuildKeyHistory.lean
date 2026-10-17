import InitECandidate.Solver.MutableTable.WitnessBuildHistory
import InitECandidate.Solver.WitnessRadix.ConstructorKeyUpdate

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open WitnessRadix

def keyRecords (plan : AllocatedLayout.Plan) (keyFor : BitVec 64 → ByteKeys.Key) (length : Nat) :
    List (Find.Key32 × BitVec 64) :=
  (List.range length).map (fun index => (keyFor (BitVec.ofNat 64 index), recordAddress plan index))

/-- Original insertion history is exactly the radix prefix's keys and real
input-record addresses, in ordinal order, including duplicate digests. -/
def KeysMatch (plan : AllocatedLayout.Plan) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (Find.Key32 × BitVec 64)) : Prop := input = keyRecords plan keyFor input.length

theorem KeysMatch.empty (plan : AllocatedLayout.Plan) (keyFor : BitVec 64 → ByteKeys.Key) :
    KeysMatch plan keyFor [] := rfl

theorem KeysMatch.snoc (plan : AllocatedLayout.Plan) (layout : BackingLayout.Layout)
    (valid : BackingLayout.Valid layout) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (Find.Key32 × BitVec 64)) (prior : KeysMatch plan keyFor input)
    (key : ByteKeys.Key) (inside : input.length < layout.count) :
    KeysMatch plan (Constructor.setKey keyFor input.length key)
      (input ++ [(key, recordAddress plan input.length)]) := by
  unfold KeysMatch
  simp only [List.length_append, List.length_singleton, keyRecords, List.range_succ,
    List.map_append, List.map_singleton, Constructor.setKey_current]
  change input ++ [(key, recordAddress plan input.length)] =
    ((List.range input.length).map (fun index =>
      (Constructor.setKey keyFor input.length key (BitVec.ofNat 64 index), recordAddress plan index))) ++
        [(key, recordAddress plan input.length)]
  congr 1
  calc
    input = keyRecords plan keyFor input.length := prior
    _ = _ := by
      unfold keyRecords
      apply List.map_congr_left
      intro index member
      rw [Constructor.setKey_earlier layout valid keyFor input.length key inside index (List.mem_range.mp member)]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.KeysMatch.empty
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.KeysMatch.snoc
