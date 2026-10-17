import InitECandidate.Solver.WitnessRadix.CapacityExactEntry
import Flapjack.FiniteMap.MapKeys

namespace InitECandidate.Solver.WitnessRadix.Capacity
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem exponent_unique (count left right : Nat) (leftLow : 2 ≤ left) (rightLow : 2 ≤ right)
    (leftEnough : 2*count+2 ≤ 2^left) (rightEnough : 2*count+2 ≤ 2^right)
    (leftUpper : 2^left < 4*count+4 ∨ left=2) (rightUpper : 2^right < 4*count+4 ∨ right=2) :
    left=right := by
  have impossible (a b : Nat) (low : 2 ≤ a) (enough : 2*count+2 ≤ 2^a)
      (upper : 2^b < 4*count+4 ∨ b=2) (smaller : a < b) : False := by
    have power : 2^(a+1) ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at power
    rcases upper with strict | same <;> omega
  by_cases smaller : left < right
  · exact False.elim (impossible left right leftLow leftEnough rightUpper smaller)
  · by_cases greater : right < left
    · exact False.elim (impossible right left rightLow rightEnough leftUpper greater)
    · omega

/-- Two actual cap=4 declarations/doubling prefixes choose the same capacity
and spend the same number of source clocks, while retaining caller locals and
every nonlocal field. Their continuations and unrelated code may differ. -/
theorem declare_paired {F : Type} (source right : PanSemStateFiniteExact 64 F)
    (count : Nat) (small : count < 2^31)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (locals : source.locals=right.locals) (leftClock : 30 ≤ source.clock) (rightClock : 30 ≤ right.clock)
    (leftTail rightTail : ProgHOL 64) :
    ∃ leftTarget rightTarget paid bits,
      evaluateHOLFiniteState source (.dec (ofString "cap") .one (.const 4#64) (.seq Constructor.capacityLoop leftTail)) =
        (let output := evaluateHOLFiniteState leftTarget leftTail; (output.1,restore source "cap" output.2)) ∧
      evaluateHOLFiniteState right (.dec (ofString "cap") .one (.const 4#64) (.seq Constructor.capacityLoop rightTail)) =
        (let output := evaluateHOLFiniteState rightTarget rightTail; (output.1,restore right "cap" output.2)) ∧
      paid ≤ 30 ∧ 2 ≤ bits ∧ bits ≤ 32 ∧ 2*count+2 ≤ 2^bits ∧ 2^bits ≤ 4*count+4 ∧
      leftTarget.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      rightTarget.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2^bits)))) ∧
      leftTarget.locals=rightTarget.locals ∧
      emptyLocalsHOLFinite leftTarget=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      emptyLocalsHOLFinite rightTarget=emptyLocalsHOLFinite {right with clock:=right.clock-paid} ∧
      (∀ name,ofString "cap"≠name→leftTarget.locals.lookup name=source.locals.lookup name) ∧
      (∀ name,ofString "cap"≠name→rightTarget.locals.lookup name=right.locals.lookup name) := by
  have rightCount : right.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) := by
    rw [← locals]; exact countLocal
  obtain ⟨leftTarget,leftPaid,leftBits,leftRun,leftBudget,leftLow,leftTop,leftEnough,leftUpper,leftCap,leftFrame,leftOther,leftExp,leftMinimal⟩ :=
    declare_execute source count small countLocal leftClock leftTail
  obtain ⟨rightTarget,rightPaid,rightBits,rightRun,rightBudget,rightLow,rightTop,rightEnough,rightUpper,rightCap,rightFrame,rightOther,rightExp,rightMinimal⟩ :=
    declare_execute right count small rightCount rightClock rightTail
  have bitsEq := exponent_unique count leftBits rightBits leftLow rightLow leftEnough rightEnough leftMinimal rightMinimal
  have paidEq : leftPaid=rightPaid := by omega
  rw [← bitsEq] at rightCap
  rw [← paidEq] at rightFrame
  have finalLocals : leftTarget.locals=rightTarget.locals := by
    apply HolFiniteMapExact.ext_lookup
    intro name
    by_cases same : ofString "cap"=name
    · subst name
      rw [leftCap,rightCap]
    · rw [leftOther name same,rightOther name same,locals]
  exact ⟨leftTarget,rightTarget,leftPaid,leftBits,leftRun,rightRun,leftBudget,leftLow,leftTop,leftEnough,leftUpper,
    leftCap,rightCap,finalLocals,leftFrame,rightFrame,leftOther,rightOther⟩

end InitECandidate.Solver.WitnessRadix.Capacity

#print axioms InitECandidate.Solver.WitnessRadix.Capacity.exponent_unique
#print axioms InitECandidate.Solver.WitnessRadix.Capacity.declare_paired
