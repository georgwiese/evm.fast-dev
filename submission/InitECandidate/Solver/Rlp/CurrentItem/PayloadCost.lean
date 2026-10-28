import InitECandidate.Solver.Rlp.CurrentItem.Entry
import InitECandidate.Solver.Rlp.CurrentListCount.Call

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem fail_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (code : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) : (evaluateHOLFiniteState source (Header.fail code)).1≠none := by
  intro normal
  exact Fail.call_not_normal source _ installed [.const code] (Prod.ext normal rfl)

theorem short_count_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length payload : BitVec 64)
    (entry : Entry source pointer length)
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (bounded : payload.toNat≤length.toNat-1)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source shortCount).2.clock≤46*length.toNat+1 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.op .add [localVar "p",.const 1#64],localVar "n"]=some (Header.values (pointer+1#64) payload) := by
    simp [Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.pointerCell,payloadCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (pointer+1#64).toNat=pointer.toNat+1 := BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; have := entry.nonempty; have := entry.fits; omega)
  have fits : (pointer+1#64).toNat+payload.toNat<2^64 := by rw [number]; have := entry.fits; have := entry.nonempty; omega
  have actual := CurrentListCount.call_cost source (pointer+1#64) payload entry.arena fits (some none) _ args
  change source.clock-(evaluateHOLFiniteState source shortCount).2.clock≤_ at actual
  omega

theorem short_tail_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length payload : BitVec 64)
    (entry : Entry source pointer length)
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.seq Header.shortGuard (.seq shortCount (shortReturn 1#64)))).2.clock≤46*length.toNat+1 := by
  have leftRead : eval source (.op .sub [localVar "len",.const 1#64])=some (.val (.word (length-1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,entry.lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval source (localVar "n")=some (.val (.word payload)) := by simp [eval,evalHOLExact,localVar,toExact,payloadCell]
  have actual := Input.ClockCost.stopping_guard_reached source (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "n"))
    (Header.fail 3#64) (.seq shortCount (shortReturn 1#64)) 1 (46*length.toNat+1) (fail_stops source 3#64 installed)
    (Fail.call_price source.code installed [.const 3#64] source rfl) ?_
  · exact Nat.le_trans actual (by omega)
  · intro passed
    have bounded := (Fail.lower_guard source source _ _ (length-1#64) payload [.const 3#64] leftRead rightRead installed passed).1
    have number : (length-1#64).toNat=length.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact entry.nonempty)
    rw [number] at bounded
    exact Input.ClockCost.sequence_current source shortCount (shortReturn 1#64) (46*length.toNat+1) 0
      (short_count_price source pointer length payload entry payloadCell bounded installed) (Input.ClockCost.returned source.code _)

theorem long_count_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length ll payload : BitVec 64)
    (entry : Entry source pointer length)
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (llBound : ll.toNat≤length.toNat-1) (bounded : payload.toNat≤length.toNat-1-ll.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source longCount).2.clock≤46*length.toNat+1 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n"]=
      some (Header.values (pointer+1#64+ll) payload) := by
    simp [Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.pointerCell,llCell,payloadCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  have number1 : (pointer+1#64).toNat=pointer.toNat+1 := BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; have := entry.fits; have := entry.nonempty; omega)
  have number : (pointer+1#64+ll).toNat=pointer.toNat+1+ll.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [number1]; have := entry.fits; have := entry.nonempty; omega),number1]
  have fits : (pointer+1#64+ll).toNat+payload.toNat<2^64 := by rw [number]; have := entry.fits; have := entry.nonempty; omega
  have actual := CurrentListCount.call_cost source (pointer+1#64+ll) payload entry.arena fits (some none) _ args
  change source.clock-(evaluateHOLFiniteState source longCount).2.clock≤_ at actual
  omega

theorem after_read_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length ll payload flag : BitVec 64)
    (entry : Entry source pointer length)
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (llBound : ll.toNat≤length.toNat-1)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (afterRead flag)).2.clock≤46*length.toNat+1 := by
  have number1 : (length-1#64).toNat=length.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact entry.nonempty)
  have number : (length-1#64-ll).toNat=length.toNat-1-ll.toNat := by
    rw [BitVec.toNat_sub_of_le (by change ll.toNat≤(length-1#64).toNat; rw [number1]; exact llBound),number1]
  have leftRead : eval source (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"])=some (.val (.word (length-1#64-ll))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,entry.lengthCell,llCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval source (localVar "n")=some (.val (.word payload)) := by simp [eval,evalHOLExact,localVar,toExact,payloadCell]
  have extentPrice : source.clock-(evaluateHOLFiniteState source
      (.seq (.ite (.cmp .lower (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"]) (localVar "n")) (Header.fail 3#64) .skip) (longTail flag))).2.clock≤46*length.toNat+1 := by
    have actual := Input.ClockCost.stopping_guard_reached source
      (.cmp .lower (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"]) (localVar "n")) (Header.fail 3#64) (longTail flag) 1 (46*length.toNat+1)
      (fail_stops source 3#64 installed) (Fail.call_price source.code installed [.const 3#64] source rfl) ?_
    · exact Nat.le_trans actual (by omega)
    · intro passed
      have bounded := (Fail.lower_guard source source _ _ (length-1#64-ll) payload [.const 3#64] leftRead rightRead installed passed).1
      rw [number] at bounded
      rw [longTail]
      split
      · exact Nat.le_trans (Input.ClockCost.returned source.code _ source rfl) (by omega)
      · exact Input.ClockCost.sequence_current source longCount (longReturn flag) (46*length.toNat+1) 0
          (long_count_price source pointer length ll payload entry llCell payloadCell llBound bounded installed) (Input.ClockCost.returned source.code _)
  have actual := Input.ClockCost.stopping_guard_current source (.cmp .notLower (.const 55#64) (localVar "n")) (Header.fail 5#64) _ 1 (46*length.toNat+1)
    (fail_stops source 5#64 installed) (Fail.call_price source.code installed [.const 5#64] source rfl) extentPrice
  exact Nat.le_trans actual (by omega)

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.fail_stops
#print axioms InitECandidate.Solver.Rlp.CurrentItem.short_count_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.short_tail_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.long_count_price
#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_read_price
