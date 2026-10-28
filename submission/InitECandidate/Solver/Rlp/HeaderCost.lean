import InitECandidate.Solver.Rlp.HeaderControl
import InitECandidate.Solver.Rlp.HeaderPrices

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (byte : UInt8)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterByte).2.clock≤10 := by
  have byteSmall : byte.toNat<256 := byte.toNat_lt_size
  have number : (BitVec.ofNat 64 byte.toNat).toNat=byte.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [after_byte_evaluate source (BitVec.ofNat 64 byte.toNat) byteCell]
  simp only [number]
  split_ifs with singleCase shortStringCase longStringCase shortListCase
  · exact Nat.le_trans (single_price source.code source rfl) (by decide)
  · exact Nat.le_trans (short_string_price source.code installed source rfl) (by decide)
  · rw [long_string_shape]
    have difference : BitVec.ofNat 64 byte.toNat-183#64=BitVec.ofNat 64 (byte.toNat-183) :=
      BitVec.ofNat_sub_ofNat_of_le byte.toNat 183 (by omega) (by omega)
    exact long_case_price source pointer (BitVec.ofNat 64 byte.toNat) 183#64 0#64 (byte.toNat-183) pointerCell byteCell difference (by omega) installed
  · exact Nat.le_trans (short_list_price source.code installed source rfl) (by decide)
  · rw [long_list_shape]
    have difference : BitVec.ofNat 64 byte.toNat-247#64=BitVec.ofNat 64 (byte.toNat-247) :=
      BitVec.ofNat_sub_ofNat_of_le byte.toNat 247 (by omega) (by omega)
    exact long_case_price source pointer (BitVec.ofNat 64 byte.toNat) 247#64 1#64 (byte.toNat-247) pointerCell byteCell difference (by omega) installed

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤10 := by
  classical
  cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer with
  | none =>
    have read : eval source (.loadByte (localVar "p"))=none := by
      simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
    rw [byte_shape,evaluateHOLFiniteState_dec_total]
    simp only
    simp only [eval] at read
    rw [read]
    simp
  | some byte =>
    have read : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
      simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
    let entered := bind source "b" (BitVec.ofNat 64 byte.toNat)
    have currentPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
      (bind_lookup_other source "b" "p" _ (by decide)).trans pointerCell
    have currentByte : entered.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := bind_lookup_same _ _ _
    rw [byte_shape]
    exact Input.ClockCost.declared_current source "b" _ _ _ 10 read (after_byte_cost entered pointer byte currentPointer currentByte installed)

/-- Complete original rlp_item_header on every outcome. The real first-byte
range and selected source guards derive length-of-length<=8; malformed or
unmapped bytes may stop earlier. No future helper run/funding is supplied. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤10 := by
  have firstCost := Fail.call_price source.code installed [.const 1#64] source rfl
  have stops : (evaluateHOLFiniteState source (fail 1#64)).1≠none := by
    intro normal
    exact Fail.call_not_normal source _ installed [.const 1#64] (Prod.ext normal rfl)
  rw [body_shape]
  exact Input.ClockCost.stopping_guard_current source _ (fail 1#64) afterGuard 1 10 stops firstCost (after_guard_cost source pointer pointerCell installed)

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.after_byte_cost
#print axioms InitECandidate.Solver.Rlp.Header.after_guard_cost
#print axioms InitECandidate.Solver.Rlp.Header.body_cost
