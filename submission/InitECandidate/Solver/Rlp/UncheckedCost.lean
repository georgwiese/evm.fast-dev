import InitECandidate.Solver.Rlp.UncheckedControl
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Rlp.Unchecked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem long_case_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer byte base : BitVec 64) (llName nName : String) (llSize : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (notP : ofString llName≠ofString "p") (difference : byte-base=BitVec.ofNat 64 llSize) (small : llSize≤8)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (longCase base llName nName)).2.clock≤9 := by
  have read : eval source (.op .sub [localVar "b",.const base])=some (.val (.word (BitVec.ofNat 64 llSize))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [longCase]
  apply Input.ClockCost.declared_current source llName _ (BitVec.ofNat 64 llSize) _ 9 read
  let ready := bind source llName (BitVec.ofNat 64 llSize)
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := (bind_lookup_other _ llName "p" _ notP).trans pointerCell
  have currentLl : ready.locals.lookup (ofString llName)=some (.val (.word (BitVec.ofNat 64 llSize))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) [.op .add [localVar "p",.const 1#64],localVar llName]=some (ReadLength.values (pointer+1#64) llSize) := by
    simp [ReadLength.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentPointer,currentLl,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact ReadLength.scoped_cost ready (pointer+1#64) llSize small (ofString nName) _ _ 0 args installed (Input.ClockCost.returned source.code _)

theorem after_byte_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (byte : UInt8)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterByte).2.clock≤9 := by
  have byteSmall : byte.toNat<256 := byte.toNat_lt_size
  have number : (BitVec.ofNat 64 byte.toNat).toNat=byte.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [after_byte_evaluate source (BitVec.ofNat 64 byte.toNat) byteCell]
  simp only [number]
  split_ifs with singleCase shortStringCase longStringCase shortListCase
  · rw [single_shape]
    exact Nat.le_trans (Input.ClockCost.returned source.code _ source rfl) (by decide)
  · rw [short_string_shape]
    exact Nat.le_trans (Input.ClockCost.returned source.code _ source rfl) (by decide)
  · rw [long_string_shape]
    exact long_case_price source pointer (BitVec.ofNat 64 byte.toNat) 183#64 "ll" "n" (byte.toNat-183) pointerCell byteCell (by decide)
      (BitVec.ofNat_sub_ofNat_of_le byte.toNat 183 (by omega) (by omega)) (by omega) installed
  · rw [short_list_shape]
    exact Nat.le_trans (Input.ClockCost.returned source.code _ source rfl) (by decide)
  · rw [long_list_shape]
    exact long_case_price source pointer (BitVec.ofNat 64 byte.toNat) 247#64 "ll2" "n2" (byte.toNat-247) pointerCell byteCell (by decide)
      (BitVec.ofNat_sub_ofNat_of_le byte.toNat 247 (by omega) (by omega)) (by omega) installed

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤9 := by
  cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer with
  | none =>
    have read : eval source (.loadByte (localVar "p"))=none := by simp [eval,evalHOLExact,localVar,toExact,pointerCell,loaded]
    rw [body_shape,evaluateHOLFiniteState_dec_total]
    simp only
    simp only [eval] at read
    rw [read]
    simp
  | some byte =>
    have read : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
      simp [eval,evalHOLExact,localVar,toExact,pointerCell,loaded]
    let ready := bind source "b" (BitVec.ofNat 64 byte.toNat)
    have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := (bind_lookup_other _ "b" "p" _ (by decide)).trans pointerCell
    rw [body_shape]
    exact Input.ClockCost.declared_current source "b" _ _ _ 9 read (after_byte_cost ready pointer byte currentPointer (bind_lookup_same _ _ _) installed)

/-- Uniform original unchecked-reader bound, even for ill-typed/missing
caller inputs. Such inputs fail before spending any helper clock. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 9 := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  cases cell : source.locals.lookup (ofString "p") with
  | none => simp [body_shape,evaluateHOLFiniteState_dec_total,evalHOLExact,localVar,toExact,cell]
  | some value =>
    cases value with
    | val word =>
      cases word with
      | word pointer => exact body_cost source pointer cell currentInstalled
    | rStruct fields => simp [body_shape,evaluateHOLFiniteState_dec_total,evalHOLExact,localVar,toExact,cell]
    | nStruct name fields => simp [body_shape,evaluateHOLFiniteState_dec_total,evalHOLExact,localVar,toExact,cell]

theorem scoped_price (code) (installed : Input.OriginalCode.Installed code) (name : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tail : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.decCall name shape (ofString "rlp_item_total_unchecked") arguments continuation) (9+tailPrice+1) :=
  Input.ClockCost.scoped_body code name shape (ofString "rlp_item_total_unchecked") arguments continuation [(ofString "p",.one)] body .one 9 tailPrice
    (original_code code installed) (body_price code installed) tail

end InitECandidate.Solver.Rlp.Unchecked

#print axioms InitECandidate.Solver.Rlp.Unchecked.long_case_price
#print axioms InitECandidate.Solver.Rlp.Unchecked.after_byte_cost
#print axioms InitECandidate.Solver.Rlp.Unchecked.body_cost
#print axioms InitECandidate.Solver.Rlp.Unchecked.body_price
#print axioms InitECandidate.Solver.Rlp.Unchecked.scoped_price
