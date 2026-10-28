import InitECandidate.Solver.Rlp.CurrentItem.PayloadCost
import InitECandidate.Solver.Rlp.HeaderPrices
import InitECandidate.Solver.Rlp.ReadLengthCall
import InitECandidate.Solver.Input.ScalarWordShape

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem single_price (code) : Input.ClockCost.Bound code single 0 := by
  rw [single_shape]
  exact Input.ClockCost.returned code _

theorem short_string_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code shortString 1 := by
  rw [short_string_shape]
  apply Input.ClockCost.declared
  exact Fail.guard_price code installed _ _ _ 1
    (Input.ClockCost.sequence code Header.canonicalGuard (shortReturn 0#64) 1 0 (Header.canonical_price code installed) (Input.ClockCost.returned code _))

theorem short_list_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte : BitVec 64)
    (entry : Entry source pointer length)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source shortList).2.clock≤46*length.toNat+1 := by
  have read : eval source (.op .sub [localVar "b",.const 192#64])=some (.val (.word (byte-192#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_list_shape]
  exact Input.ClockCost.declared_current source "n" _ (byte-192#64) _ (46*length.toNat+1) read
    (short_tail_price (bind source "n" (byte-192#64)) pointer length (byte-192#64)
      (Entry.bound_word source pointer length (byte-192#64) "n" entry (by decide) (by decide)) (bind_lookup_same _ _ _) installed)

theorem long_case_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte base flag : BitVec 64) (llNat : Nat)
    (entry : Entry source pointer length)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (difference : byte-base=BitVec.ofNat 64 llNat) (small : llNat≤8)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (longCase base flag)).2.clock≤46*length.toNat+10 := by
  have read : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (BitVec.ofNat 64 llNat))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [longCase]
  apply Input.ClockCost.declared_current source "ll" _ (BitVec.ofNat 64 llNat) _ (46*length.toNat+10) read
  let entered := bind source "ll" (BitVec.ofNat 64 llNat)
  have enteredEntry : Entry entered pointer length := Entry.bound_word source pointer length (BitVec.ofNat 64 llNat) "ll" entry (by decide) (by decide)
  have llCell : entered.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llNat))) := bind_lookup_same _ _ _
  have leftRead : eval entered (.op .sub [localVar "len",.const 1#64])=some (.val (.word (length-1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,enteredEntry.lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval entered (localVar "ll")=some (.val (.word (BitVec.ofNat 64 llNat))) := by simp [eval,evalHOLExact,localVar,toExact,llCell]
  have actual := Input.ClockCost.stopping_guard_reached entered (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "ll")) (Header.fail 3#64)
    (.decCall (ofString "n") .one (ofString "rlp_read_length") Header.readArguments (afterRead flag)) 1 (46*length.toNat+10)
    (fail_stops entered 3#64 installed) (Fail.call_price source.code installed [.const 3#64] entered rfl) ?_
  · exact Nat.le_trans actual (by omega)
  · intro passed
    have llBound := (Fail.lower_guard entered entered _ _ (length-1#64) (BitVec.ofNat 64 llNat) [.const 3#64] leftRead rightRead installed passed).1
    have remaining : (length-1#64).toNat=length.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact entry.nonempty)
    rw [remaining] at llBound
    have args : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) Header.readArguments=some (ReadLength.values (pointer+1#64) llNat) := by
      simp [Header.readArguments,ReadLength.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,enteredEntry.pointerCell,llCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := ReadLength.environment entered.code.lookup (pointer+1#64) llNat (ReadLength.original_code entered.code installed)
    have price := Input.ClockCost.scoped_reached_current entered "n" .one (ofString "rlp_read_length") Header.readArguments _ ReadLength.body (afterRead flag) callee .one 8 (46*length.toNat+1) args called
      (ReadLength.body_cost_eight (callEntryStateHOLFinite entered callee) llNat small lengthLocal installed) ?_
    · omega
    · intro calleePost returned run checked
      have fields := ReadLength.readonly entered.code installed (callEntryStateHOLFinite entered callee) rfl
      rw [run] at fields
      change Input.LocalEffects.erase calleePost=Input.LocalEffects.erase entered at fields
      have shapePass : shapeEqHOL (shapeOfHOLExact returned) .one=true := by
        cases observed : shapeEqHOL (shapeOfHOLExact returned) .one <;> simp_all
      have shape : shapeOfHOLExact returned=.one := (shapeEqHOL_eq_true _ _).mp shapePass
      obtain ⟨payload,same⟩ := Input.scalar_word_of_shape returned shape
      rw [same]
      let ready := bind {calleePost with locals:=entered.locals} "n" payload
      have readyEntry : Entry ready pointer length := Entry.readonly_resume entered calleePost pointer length "n" (.val (.word payload)) enteredEntry fields (by decide) (by decide)
      have currentLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 llNat))) :=
        (bind_lookup_other _ "n" "ll" _ (by decide)).trans llCell
      have codeEq := congrArg PanSemStateFiniteExact.code fields
      change ready.code=entered.code at codeEq
      exact after_read_price ready pointer length (BitVec.ofNat 64 llNat) payload flag readyEntry currentLl (bind_lookup_same _ _ _) llBound (by rw [codeEq]; exact installed)

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.single_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.short_string_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.short_list_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.long_case_price
