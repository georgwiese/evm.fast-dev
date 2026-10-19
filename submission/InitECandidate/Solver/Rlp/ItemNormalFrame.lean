import InitECandidate.Solver.Rlp.ItemShortFrame
import InitECandidate.Solver.Rlp.ItemLongFrame
import InitECandidate.Solver.Rlp.ItemCost

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit byte : BitVec 64)
    (entry : Entry source pointer length cursor limit) (byteSmall : byte.toNat<256)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterByte=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Validation.Arena post cursor limit ∧ Validation.Above source post cursor.toNat := by
  rw [after_byte_evaluate source byte byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · exact single_normal_above source post pointer length cursor limit entry value normal
  · exact short_string_normal_above source post pointer length cursor limit byte entry byteCell installed value normal
  · rw [long_string_shape] at normal
    have difference : byte-183#64=BitVec.ofNat 64 (byte.toNat-183) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 183 (by decide) (by omega)
    exact long_case_normal_above source post pointer length cursor limit byte 183#64 0#64 (byte.toNat-183) entry (by omega) difference (Or.inl rfl) byteCell installed value normal
  · exact short_list_normal_above source post pointer length cursor limit byte entry byteCell installed value normal
  · rw [long_list_shape] at normal
    have difference : byte-247#64=BitVec.ofNat 64 (byte.toNat-247) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 247 (by decide) (by omega)
    exact long_case_normal_above source post pointer length cursor limit byte 247#64 1#64 (byte.toNat-247) entry (by omega) difference (Or.inr rfl) byteCell installed value normal

/-- The real original item decoder derives its actual four-word result,
binary kind, nonwrapping payload/total extent and retained arena. No decoded
item, callee output or future memory model is assumed. -/
theorem body_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Validation.Arena post cursor limit ∧ Validation.Above source post cursor.toNat ∧ source.clock-post.clock≤60*length.toNat+41 := by
  have priced := body_cost source pointer length cursor limit pointerCell lengthCell arena fits installed
  rw [normal] at priced
  rw [body_shape] at normal
  have lengthRead : eval source (localVar "len")=some (.val (.word length)) := by simp [eval,evalHOLExact,localVar,toExact,lengthCell]
  obtain ⟨nonzero,byteRun⟩ := Fail.equal_guard_return source post (localVar "len") (.const 0#64) length 0#64 [.const 1#64] afterGuard value lengthRead rfl installed normal
  have positive : 1≤length.toNat := by
    by_contra zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change length.toNat=0
    omega
  rw [byte_shape] at byteRun
  obtain ⟨declared,inner,byteRead,typed,innerRun,restored⟩ := Input.CallNormal.declaration_normal_entry source post "b" .one (.loadByte (localVar "p")) afterByte value byteRun
  obtain ⟨byte,byteEq,small⟩ := Input.byte_expression_value source (localVar "p") declared byteRead
  rw [byteEq] at innerRun
  let entered := bind source "b" byte
  have entry : Entry source pointer length cursor limit := ⟨pointerCell,lengthCell,arena,positive,fits⟩
  have nextEntry : Entry entered pointer length cursor limit := Entry.bound_word source pointer length cursor limit byte "b" entry (by decide) (by decide)
  obtain ⟨valid,nextArena,above⟩ := after_byte_normal_above entered inner pointer length cursor limit byte nextEntry small (bind_lookup_same _ _ _) installed value innerRun
  refine ⟨valid,Validation.Arena.of_fields inner post cursor limit nextArena ?_ ?_,?_,priced⟩
  · rw [restored]; rfl
  · rw [restored]; rfl
  · intro query upper
    rw [restored]
    exact above query upper

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.after_byte_normal_above
#print axioms InitECandidate.Solver.Rlp.Item.body_normal_above
