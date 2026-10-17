import InitECandidate.Solver.Input.ScalarProgram

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem list_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : List (ExpHOL 64))
    (same : List.Forall₂ (fun first second=>eval source first=eval source second) left right) :
    @evalListHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) left=
    @evalListHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) right := by
  induction same with
  | nil=>rfl
  | cons same rest ih=>
    simp only [eval] at same
    simp only [evalListHOLExact,same,ih]

theorem op_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (operator : BinOp) (left right : List (ExpHOL 64))
    (same : List.Forall₂ (fun first second=>eval source first=eval source second) left right) :
    eval source (.op operator left)=eval source (.op operator right) := by
  classical
  simp only [eval]
  rw [evalHOLExact,evalHOLExact,list_congr source left right same]

theorem byte_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : ExpHOL 64)
    (same : eval source left=eval source right) :
    eval source (.loadByte left)=eval source (.loadByte right) := by
  classical
  simp only [eval] at same ⊢
  rw [evalHOLExact,evalHOLExact,same]

theorem plus_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : ExpHOL 64) (offset : Nat)
    (same : eval source left=eval source right) :
    eval source (plus left offset)=eval source (plus right offset) :=
  op_congr source .add _ _ (.cons same (.cons rfl .nil))

theorem shift_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : ExpHOL 64) (bits : Nat)
    (same : eval source left=eval source right) :
    eval source (shift left bits)=eval source (shift right bits) := by
  classical
  simp only [eval] at same ⊢
  rw [shift,shift,evalHOLExact,evalHOLExact,same]
  rfl

theorem le32_congr {F : Type} (source : PanSemStateFiniteExact 64 F) (left right : ExpHOL 64)
    (same : eval source left=eval source right) :
    eval source (le32 left)=eval source (le32 right) := by
  apply op_congr
  exact .cons (byte_congr source _ _ same)
    (.cons (shift_congr source _ _ 8 (byte_congr source _ _ (plus_congr source _ _ 1 same)))
      (.cons (shift_congr source _ _ 16 (byte_congr source _ _ (plus_congr source _ _ 2 same)))
        (.cons (shift_congr source _ _ 24 (byte_congr source _ _ (plus_congr source _ _ 3 same))) .nil)))

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.list_congr
#print axioms InitECandidate.Solver.Input.Scalar.op_congr
#print axioms InitECandidate.Solver.Input.Scalar.byte_congr
#print axioms InitECandidate.Solver.Input.Scalar.plus_congr
#print axioms InitECandidate.Solver.Input.Scalar.shift_congr
#print axioms InitECandidate.Solver.Input.Scalar.le32_congr
