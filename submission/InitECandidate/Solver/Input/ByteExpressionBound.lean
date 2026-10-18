import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem single_argument {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (value : ValueHOL 64)
    (read : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [expression] = some [value]) :
    eval source expression = some value := by
  simp only [evalListHOLFinite, evalListHOLExact] at read
  cases actual : eval source expression with
  | none =>
      simp only [eval] at actual
      simp only [actual] at read
      cases read
  | some actualValue =>
      simp only [eval] at actual
      simp only [actual, Option.some.injEq, List.cons.injEq, and_true] at read
      exact congrArg some read

/-- An actually read byte is a real word below256, even if other source
memory words contain labels or invalid data. -/
theorem byte_expression_value {F : Type} (source : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source (.loadByte address) = some value) :
    ∃ word : BitVec 64, value = .val (.word word) ∧ word.toNat < 256 := by
  classical
  simp only [eval, evalHOLExact] at read
  split at read
  · rename_i pointer addressRead
    cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer with
    | none => simp only [loaded, Option.map_none] at read; cases read
    | some byte =>
      simp only [loaded, Option.map_some, Option.some.injEq] at read
      refine ⟨BitVec.ofNat 64 byte.toNat, read.symm, ?_⟩
      have bounded : byte.toNat < 256 := byte.toNat_lt_size
      rw [BitVec.toNat_ofNat]
      have reduced := Nat.mod_le byte.toNat (2 ^ 64)
      omega
  · cases read

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.single_argument
#print axioms InitECandidate.Solver.Input.byte_expression_value
