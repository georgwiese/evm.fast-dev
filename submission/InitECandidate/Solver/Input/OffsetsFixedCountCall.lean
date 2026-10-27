import InitECandidate.Solver.Input.OffsetsCurrentCost
import InitECandidate.Solver.Input.ClockCostCallReached

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The literal second argument remains the callee's count, irrespective of
the values or failed shape checks of the other three arguments. -/
theorem lookup_fixed_count (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (entry : code (ofString "ssz_check_offsets") = some (formals, body, .one))
    (left fixed total : ValueHOL 64) (count : Nat)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite code (ofString "ssz_check_offsets")
      [left, .val (.word (BitVec.ofNat 64 count)), fixed, total] = some (actual, callee, shape)) :
    actual = body ∧ callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) := by
  have raw := lookupCodeHOLFinite_eq_some code _ _ actual callee shape called
  simp only [lookupCodeHOLExact, entry] at raw
  split at raw
  · have same := Option.some.inj raw
    have bodyEq := congrArg Prod.fst same
    have cell := congrArg
      (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "n")) same
    exact ⟨bodyEq.symm, by
      simpa [formals, show ofString "n" ≠ ofString "len" from by decide,
        show ofString "n" ≠ ofString "fixed" from by decide] using cell.symm⟩
  · cases raw

theorem evaluated_fixed_count (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (left fixed total : ExpHOL 64) (count : Nat) (values : List (ValueHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [left, .const (BitVec.ofNat 64 count), fixed, total] = some values) :
    ∃ a b c, values = [a, .val (.word (BitVec.ofNat 64 count)), b, c] := by
  classical
  cases first : evalHOLExact source.toExact left with
  | none => simp [evalListHOLFinite, evalListHOLExact, first] at args
  | some a =>
    cases middle : evalHOLExact source.toExact fixed with
    | none => simp [evalListHOLFinite, evalListHOLExact, first, evalHOLExact, middle] at args
    | some b =>
      cases last : evalHOLExact source.toExact total with
      | none => simp [evalListHOLFinite, evalListHOLExact, first, evalHOLExact, middle, last] at args
      | some c =>
        refine ⟨a, b, c, ?_⟩
        have actual := args
        simp [evalListHOLFinite, evalListHOLExact, first, evalHOLExact, middle, last] at actual
        exact actual.symm

/-- Whole ignored validator calls with the actual literal count used by the
precheck. Other arguments may fail or be malformed; no mapping is assumed. -/
theorem call_fixed_count_cost (code) (installed : OriginalCode.Installed code)
    (count : Nat) (small : count ≤ 8) (left fixed total : ExpHOL 64) :
    ClockCost.Bound code (.call (some (none, none)) (ofString "ssz_check_offsets")
      [left, .const (BitVec.ofNat 64 count), fixed, total]) (3 * count + 2) := by
  intro source codeEq
  have currentInstalled : OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  have priced := ClockCost.call_arguments_current source (some none) (ofString "ssz_check_offsets")
    [left, .const (BitVec.ofNat 64 count), fixed, total] (3 * count + 1) (by
      intro values actual callee shape args called
      obtain ⟨a, b, c, valueEq⟩ := evaluated_fixed_count source left fixed total count values args
      rw [valueEq] at called
      obtain ⟨bodyEq, cell⟩ := lookup_fixed_count source.code.lookup
        (SszCurrentCode.offsets_installed source.code currentInstalled) a b c count actual callee shape called
      rw [bodyEq]
      exact body_cost (callEntryStateHOLFinite source callee) count small currentInstalled cell)
  simpa [Nat.add_assoc, LocalEffects.callInfo] using priced

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.lookup_fixed_count
#print axioms InitECandidate.Solver.Input.Offsets.evaluated_fixed_count
#print axioms InitECandidate.Solver.Input.Offsets.call_fixed_count_cost
