import InitECandidate.Solver.Input.FlatAddress
import InitECandidate.Solver.Input.ScalarCongr

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def flat32 (base : ExpHOL 64) (offsets : List Nat) : ExpHOL 64 :=
  .op .or [.loadByte (flatAddress base offsets),shift (.loadByte (flatAddress base (offsets++[1]))) 8,
    shift (.loadByte (flatAddress base (offsets++[2]))) 16,shift (.loadByte (flatAddress base (offsets++[3]))) 24]
def flat64 (base : ExpHOL 64) (offsets : List Nat) : ExpHOL 64 :=
  .op .or [.loadByte (flatAddress base offsets),shift (.loadByte (flatAddress base (offsets++[1]))) 8,
    shift (.loadByte (flatAddress base (offsets++[2]))) 16,shift (.loadByte (flatAddress base (offsets++[3]))) 24,
    shift (flat32 base (offsets++[4])) 32]

theorem flat_append {F : Type} (source : PanSemStateFiniteExact 64 F) (base : ExpHOL 64) (pointer : BitVec 64)
    (offsets : List Nat) (offset : Nat) (baseRead : eval source base=some (.val (.word pointer))) :
    eval source (flatAddress base (offsets++[offset]))=eval source (plus (flatAddress base offsets) offset) := by
  have first:=flat_read source base pointer (offsets++[offset]) baseRead
  have second:=plus_read source (flatAddress base offsets) (pointer+BitVec.ofNat 64 offsets.sum) offset
    (flat_read source base pointer offsets baseRead)
  rw [first,second]
  simp [List.sum_append,BitVec.ofNat_add,BitVec.add_assoc]

theorem flat32_equiv {F : Type} (source : PanSemStateFiniteExact 64 F) (base : ExpHOL 64) (pointer : BitVec 64)
    (offsets : List Nat) (baseRead : eval source base=some (.val (.word pointer))) :
    eval source (flat32 base offsets)=eval source (le32 (flatAddress base offsets)) := by
  apply op_congr
  exact .cons rfl
    (.cons (shift_congr source _ _ 8 (byte_congr source _ _ (flat_append source base pointer offsets 1 baseRead)))
      (.cons (shift_congr source _ _ 16 (byte_congr source _ _ (flat_append source base pointer offsets 2 baseRead)))
        (.cons (shift_congr source _ _ 24 (byte_congr source _ _ (flat_append source base pointer offsets 3 baseRead))) .nil)))

theorem flat64_equiv {F : Type} (source : PanSemStateFiniteExact 64 F) (base : ExpHOL 64) (pointer : BitVec 64)
    (offsets : List Nat) (baseRead : eval source base=some (.val (.word pointer))) :
    eval source (flat64 base offsets)=eval source (le64 (flatAddress base offsets)) := by
  have highEq:eval source (flat32 base (offsets++[4]))=eval source (le32 (plus (flatAddress base offsets) 4)) :=
    (flat32_equiv source base pointer (offsets++[4]) baseRead).trans
      (le32_congr source _ _ (flat_append source base pointer offsets 4 baseRead))
  apply op_congr
  exact .cons rfl
    (.cons (shift_congr source _ _ 8 (byte_congr source _ _ (flat_append source base pointer offsets 1 baseRead)))
      (.cons (shift_congr source _ _ 16 (byte_congr source _ _ (flat_append source base pointer offsets 2 baseRead)))
        (.cons (shift_congr source _ _ 24 (byte_congr source _ _ (flat_append source base pointer offsets 3 baseRead)))
          (.cons (shift_congr source _ _ 32 highEq) .nil))))

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.flat_append
#print axioms InitECandidate.Solver.Input.Scalar.flat32_equiv
#print axioms InitECandidate.Solver.Input.Scalar.flat64_equiv
