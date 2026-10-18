import InitECandidate.Solver.Input.StoreWordsNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fourWords : ShapeHOL := .comb [.one, .one, .one, .one]

theorem mem_load4_length (address : BitVec 64) (domain : BitVec 64 → Prop) (memory : BitVec 64 → HolWordLab 64) (context : StructContextHOLM)
    (value : ValueHOL 64)
    (read : @memLoadHOLExact 64 _ fourWords address domain (fun current => Classical.propDecidable (domain current)) memory context = some value) :
    (flattenHOL value).length = 4 := by
  classical
  by_cases first : domain address <;>
    by_cases second : domain (address + 8#64) <;>
    by_cases third : domain (address + 8#64 + 8#64) <;>
    by_cases fourth : domain (address + 8#64 + 8#64 + 8#64) <;>
    simp [fourWords, memLoadHOLExact, memLoadsHOLExact, bytesInWordHOL, sizeOfShapeWithContextHOL, first, second, third, fourth] at read
  subst value
  simp [flattenHOL]

theorem load4_length {F : Type} (source : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source (.load fourWords address) = some value) : (flattenHOL value).length = 4 := by
  classical
  simp only [eval, evalHOLExact] at read
  have valid : isWfShapeExactHOL source.structs fourWords = true := by simp [fourWords, isWfShapeExactHOL]
  rw [if_pos valid] at read
  split at read
  · exact mem_load4_length _ source.memaddrs source.memory source.structs value read
  · cases read

theorem load1_length {F : Type} (source : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source (.load .one address) = some value) : (flattenHOL value).length = 1 := by
  classical
  simp only [eval, evalHOLExact] at read
  have valid : isWfShapeExactHOL source.structs .one = true := by simp [isWfShapeExactHOL]
  rw [if_pos valid] at read
  split at read
  · simp only [memLoadHOLExact] at read
    split at read
    · cases read
      simp [flattenHOL]
    · cases read
  · cases read

theorem local_one_length {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (payload : HolWordLab 64) (value : ValueHOL 64)
    (stored : source.locals.lookup (ofString name) = some (.val payload))
    (read : eval source (localVar name) = some value) : (flattenHOL value).length = 1 := by
  simp only [eval, localVar, evalHOLExact, toExact, stored, Option.some.injEq] at read
  rw [← read]
  simp [flattenHOL]

theorem global_one_length {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (payload : HolWordLab 64) (value : ValueHOL 64)
    (stored : source.globals.lookup (ofString name) = some (.val payload))
    (read : eval source (.var .global (ofString name)) = some value) : (flattenHOL value).length = 1 := by
  simp only [eval, evalHOLExact, toExact, stored, Option.some.injEq] at read
  rw [← read]
  simp [flattenHOL]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.mem_load4_length
#print axioms InitECandidate.Solver.Input.load4_length
#print axioms InitECandidate.Solver.Input.load1_length

#print axioms InitECandidate.Solver.Input.local_one_length

#print axioms InitECandidate.Solver.Input.global_one_length
