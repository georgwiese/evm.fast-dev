import InitECandidate.Solver.Rlp.HeaderProgram

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem single_price (code) : Input.ClockCost.Bound code single 0 := by
  rw [single_shape]
  exact Input.ClockCost.returned code _

theorem canonical_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code canonicalGuard 1 :=
  Input.ClockCost.conditional code _ _ _ 1 0
    (Input.ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed _) (Input.ClockCost.skip code)) (Input.ClockCost.skip code)

theorem short_string_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code shortString 1 := by
  rw [short_string_shape]
  apply Input.ClockCost.declared
  exact Fail.guard_price code installed _ _ _ 1
    (Input.ClockCost.sequence code canonicalGuard (shortReturn 0#64) 1 0 (canonical_price code installed) (Input.ClockCost.returned code _))

theorem short_list_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code shortList 1 := by
  rw [short_list_shape]
  apply Input.ClockCost.declared
  exact Fail.guard_price code installed _ _ _ 0 (Input.ClockCost.returned code _)

theorem after_read_price (code) (installed : Input.OriginalCode.Installed code) (flag : BitVec 64) :
    Input.ClockCost.Bound code (afterRead flag) 1 :=
  Fail.guard_price code installed _ _ _ 1 (Fail.guard_price code installed _ _ _ 0 (Input.ClockCost.returned code _))

/-- The length-of-length comes from the current selected header byte. The
real length-reader and its canonical/extent guards are alternatives to the
initial failing guard, so the selected long case costs at most10ticks. -/
theorem long_case_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer byte base flag : BitVec 64) (length : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (difference : byte-base=BitVec.ofNat 64 length) (small : length≤8)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (longCase base flag)).2.clock≤10 := by
  have read : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (BitVec.ofNat 64 length))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [longCase]
  apply Input.ClockCost.declared_current source "ll" _ (BitVec.ofNat 64 length) _ 10 read
  let entered := bind source "ll" (BitVec.ofNat 64 length)
  have currentPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other source "ll" "p" _ (by decide)).trans pointerCell
  have currentLength : entered.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 length))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) readArguments=some (ReadLength.values (pointer+1#64) length) := by
    simp [readArguments,ReadLength.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentPointer,currentLength,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondCost := ReadLength.scoped_cost entered (pointer+1#64) length small (ofString "n") readArguments (afterRead flag) 1 args installed (after_read_price source.code installed flag)
  have firstCost := Fail.call_price source.code installed [.const 3#64] entered rfl
  have stops : (evaluateHOLFiniteState entered (fail 3#64)).1≠none := by
    intro normal
    exact Fail.call_not_normal entered _ installed [.const 3#64] (Prod.ext normal rfl)
  exact Input.ClockCost.stopping_guard_current entered _ (fail 3#64) _ 1 10 stops firstCost secondCost

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.single_price
#print axioms InitECandidate.Solver.Rlp.Header.canonical_price
#print axioms InitECandidate.Solver.Rlp.Header.short_string_price
#print axioms InitECandidate.Solver.Rlp.Header.short_list_price
#print axioms InitECandidate.Solver.Rlp.Header.after_read_price
#print axioms InitECandidate.Solver.Rlp.Header.long_case_price
