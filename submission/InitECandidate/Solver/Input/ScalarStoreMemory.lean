import InitECandidate.Solver.Input.ScalarNormal

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

/-- Normal stores of successful scalar expressions touch one literal word.
The expression's actual evaluated data is derived from the same store. -/
theorem scalar_store_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (address expression : ExpHOL 64) (pointer query : BitVec 64)
    (read : eval source address=some (.val (.word pointer)))
    (scalar : ∀ value,eval source expression=some value → (flattenHOL value).length≤1)
    (away : query≠pointer) (run : evaluateHOLFiniteState source (.store address expression)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨value,memory,evaluated,stored,endpoint⟩ := store_at_normal source post address expression pointer read run
  rw [endpoint]
  apply words_away (flattenHOL value) pointer query source.memaddrs source.memory memory stored
  intro index inside
  have lengthBound := scalar value evaluated
  have zero : index=0 := by omega
  simpa only [zero,Nat.mul_zero,BitVec.add_zero] using away

theorem op_store_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (operator : BinOp) (arguments : List (ExpHOL 64)) (pointer query : BitVec 64)
    (read : eval source address=some (.val (.word pointer))) (away : query≠pointer)
    (run : evaluateHOLFiniteState source (.store address (.op operator arguments))=(none,post)) : post.memory query=source.memory query :=
  scalar_store_normal source post address _ pointer query read (by intro value evaluated; rw [Input.op_length source operator arguments value evaluated]; exact Nat.le_refl 1) away run

theorem shift_length {F : Type} (source : PanSemStateFiniteExact 64 F) (operator : Shift) (left right : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source (.shift operator left right)=some value) : (flattenHOL value).length=1 := by
  classical
  simp only [eval] at read
  rw [evalHOLExact] at read
  split at read
  · rename_i leftWord rightWord leftRead rightRead
    cases shifted : wordShiftHOL operator leftWord rightWord.toNat with
    | none=>simp [shifted] at read
    | some word=>
      simp only [shifted,Option.map_some,Option.some.injEq] at read
      rw [←read]
      simp [flattenHOL]
  · cases read

theorem shift_store_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (operator : Shift) (left right : ExpHOL 64) (pointer query : BitVec 64)
    (read : eval source address=some (.val (.word pointer))) (away : query≠pointer)
    (run : evaluateHOLFiniteState source (.store address (.shift operator left right))=(none,post)) : post.memory query=source.memory query :=
  scalar_store_normal source post address _ pointer query read (by intro value evaluated; rw [shift_length source operator left right value evaluated]; exact Nat.le_refl 1) away run

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.scalar_store_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.op_store_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.shift_length
#print axioms InitECandidate.Solver.Input.MemoryAt.shift_store_normal
