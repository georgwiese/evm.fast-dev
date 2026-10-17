import InitECandidate.Solver.Input.VarList.Walk

namespace InitECandidate.Solver.Input.VarList
open Flapjack

theorem Plan.row_eq_iff {input : Guest.InputBlob} (plan : Plan input) (left right : Nat)
    (l : left<plan.count) (r : right<plan.count) : row plan.array left=row plan.array right↔left=right := by
  constructor
  · intro eq
    have h:=congrArg BitVec.toNat eq
    rw [plan.row_nat left l,plan.row_nat right r] at h
    omega
  · intro eq
    rw [eq]

theorem Plan.length_eq_iff {input : Guest.InputBlob} (plan : Plan input) (left right : Nat)
    (l : left<plan.count) (r : right<plan.count) : lengthCell plan.array left=lengthCell plan.array right↔left=right := by
  constructor
  · intro eq
    have h:=congrArg BitVec.toNat eq
    rw [plan.length_nat left l,plan.length_nat right r] at h
    omega
  · intro eq
    rw [eq]

theorem Plan.row_ne_length {input : Guest.InputBlob} (plan : Plan input) (left right : Nat)
    (l : left<plan.count) (r : right<plan.count) : row plan.array left≠lengthCell plan.array right := by
  intro eq
  have h:=congrArg BitVec.toNat eq
  rw [plan.row_nat left l,plan.length_nat right r] at h
  omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Plan.row_eq_iff
#print axioms InitECandidate.Solver.Input.VarList.Plan.length_eq_iff
#print axioms InitECandidate.Solver.Input.VarList.Plan.row_ne_length
