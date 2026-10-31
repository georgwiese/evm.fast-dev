import InitECandidate.Solver.Rlp.CurrentItem.CasePrices
import InitECandidate.Solver.Rlp.ItemControl

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (byte : UInt8)
    (entry : Entry source pointer length)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterByte).2.clock≤60*length.toNat+10 := by
  have byteSmall : byte.toNat<256 := byte.toNat_lt_size
  have number : (BitVec.ofNat 64 byte.toNat).toNat=byte.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [after_byte_evaluate source (BitVec.ofNat 64 byte.toNat) byteCell]
  simp only [number]
  split_ifs with singleCase shortStringCase longStringCase shortListCase
  · exact Nat.le_trans (single_price source.code source rfl) (by omega)
  · exact Nat.le_trans (short_string_price source.code installed source rfl) (by omega)
  · rw [long_string_shape]
    have difference : BitVec.ofNat 64 byte.toNat-183#64=BitVec.ofNat 64 (byte.toNat-183) :=
      BitVec.ofNat_sub_ofNat_of_le byte.toNat 183 (by omega) (by omega)
    exact long_case_price source pointer length (BitVec.ofNat 64 byte.toNat) 183#64 0#64 (byte.toNat-183) entry byteCell difference (by omega) installed
  · exact Nat.le_trans (short_list_price source pointer length (BitVec.ofNat 64 byte.toNat) entry byteCell installed) (by omega)
  · rw [long_list_shape]
    have difference : BitVec.ofNat 64 byte.toNat-247#64=BitVec.ofNat 64 (byte.toNat-247) :=
      BitVec.ofNat_sub_ofNat_of_le byte.toNat 247 (by omega) (by omega)
    exact long_case_price source pointer length (BitVec.ofNat 64 byte.toNat) 247#64 1#64 (byte.toNat-247) entry byteCell difference (by omega) installed

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Entry source pointer length) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤60*length.toNat+10 := by
  cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer with
  | none =>
    have read : eval source (.loadByte (localVar "p"))=none := by simp [eval,localVar,evalHOLExact,toExact,entry.pointerCell,loaded]
    rw [byte_shape,evaluateHOLFiniteState_dec_total]
    simp only
    simp only [eval] at read
    rw [read]
    simp
  | some byte =>
    have read : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
      simp [eval,localVar,evalHOLExact,toExact,entry.pointerCell,loaded]
    let entered := bind source "b" (BitVec.ofNat 64 byte.toNat)
    have nextEntry : Entry entered pointer length := Entry.bound_word source pointer length (BitVec.ofNat 64 byte.toNat) "b" entry (by decide) (by decide)
    rw [byte_shape]
    exact Input.ClockCost.declared_current source "b" _ _ _ (60*length.toNat+10) read
      (after_byte_cost entered pointer length byte nextEntry (bind_lookup_same _ _ _) installed)

/-- Complete unchanged current Software rlp_item95, including nested list counting
and validation. All outcomes are covered from the current physical arena and
nonwrapping input extent; byte contents, mapping and funding are unrestricted. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Input.CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*length.toNat+10 := by
  rw [body_shape]
  have actual := Input.ClockCost.stopping_guard_reached source (.cmp .equal (localVar "len") (.const 0#64)) (Header.fail 1#64) afterGuard 1 (60*length.toNat+10)
    (fail_stops source 1#64 installed) (Fail.call_price source.code installed [.const 1#64] source rfl) ?_
  · exact Nat.le_trans actual (by omega)
  · intro passed
    have leftRead : eval source (localVar "len")=some (.val (.word length)) := by simp [eval,evalHOLExact,localVar,toExact,lengthCell]
    have nonzero := (Fail.equal_guard source source (localVar "len") (.const 0#64) length 0#64 [.const 1#64] leftRead rfl installed passed).1
    have positive : 1≤length.toNat := by
      by_contra zero
      have number : length.toNat=0 := by omega
      have wordZero : length=0#64 := BitVec.eq_of_toNat_eq number
      exact nonzero wordZero
    exact after_guard_cost source pointer length ⟨pointerCell,lengthCell,arena,positive,fits⟩ installed

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_byte_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_guard_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItem.body_cost
