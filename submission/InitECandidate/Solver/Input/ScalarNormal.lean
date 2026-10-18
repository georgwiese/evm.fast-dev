import InitECandidate.Solver.Input.StoreWordsNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem op_length {F : Type} (source : PanSemStateFiniteExact 64 F) (operation : BinOp) (arguments : List (ExpHOL 64)) (value : ValueHOL 64)
    (read : eval source (.op operation arguments) = some value) : (flattenHOL value).length = 1 := by
  classical
  simp only [eval] at read
  rw [evalHOLExact] at read
  cases args : evalListHOLExact source.toExact arguments with
  | none => simp [args] at read
  | some values =>
    simp only [args] at read
    by_cases allWords : values.all valueIsWord = true
    · rw [if_pos allWords] at read
      cases result : wordOpHOL operation (values.map valueWord) with
      | none => simp [result] at read
      | some word =>
        simp only [result, Option.map_some, Option.some.injEq] at read
        rw [← read]
        simp [flattenHOL]
    · rw [if_neg allWords] at read
      cases read

theorem load_one_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (address : BitVec 64) (value : ValueHOL 64)
    (addressRead : eval source expression = some (.val (.word address)))
    (read : eval source (.load .one expression) = some value) : source.memaddrs address := by
  classical
  simp only [eval] at addressRead read
  rw [evalHOLExact, if_pos (by simp [isWfShapeExactHOL]), addressRead] at read
  by_cases mapped : source.memaddrs address
  · exact mapped
  · simp [memLoadHOLExact, mapped, toExact] at read

theorem stores_nonempty_mapped (values : List (HolWordLab 64)) (address : BitVec 64) (domain : BitVec 64 → Prop)
    (memory output : BitVec 64 → HolWordLab 64) (positive : 0 < values.length)
    (normal : @panMemStoresHOL 64 _ address values domain (fun current => Classical.propDecidable (domain current)) memory = some output) : domain address := by
  classical
  cases values with
  | nil => simp at positive
  | cons value rest =>
    by_cases mapped : domain address
    · exact mapped
    · simp [panMemStoresHOL, panMemStoreHOL, mapped] at normal

/-- A normal nonempty store derives its destination mapping from its actual
write list. No ordinary-domain or speculative write-success premise. -/
theorem store_mapped_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64) (address : BitVec 64)
    (addressRead : eval source destination = some (.val (.word address)))
    (positive : ∀ value, eval source expression = some value → 0 < (flattenHOL value).length)
    (normal : evaluateHOLFiniteState source (.store destination expression) = (none, target)) : source.memaddrs address := by
  obtain ⟨value, memory, read, stores, frame⟩ := store_at_normal source target destination expression address addressRead normal
  exact stores_nonempty_mapped (flattenHOL value) address source.memaddrs source.memory memory (positive value read) stores

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.op_length
#print axioms InitECandidate.Solver.Input.load_one_mapped
#print axioms InitECandidate.Solver.Input.stores_nonempty_mapped
#print axioms InitECandidate.Solver.Input.store_mapped_normal
