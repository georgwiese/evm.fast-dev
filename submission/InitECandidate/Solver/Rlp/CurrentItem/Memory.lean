import InitECandidate.Solver.Rlp.CurrentItem.ShortNormal
import InitECandidate.Solver.Rlp.CurrentItem.LongNormal
import InitECandidate.Solver.Rlp.CurrentItem.Cost

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte : BitVec 64)
    (entry : Entry source pointer length) (byteSmall : byte.toNat<256)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterByte=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Frame source post := by
  rw [after_byte_evaluate source byte byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · obtain ⟨valid,pure⟩ := single_normal source post pointer length entry value normal
    exact ⟨valid,Frame.of_readonly pure⟩
  · obtain ⟨valid,pure⟩ := short_string_normal source post pointer length byte entry byteCell installed value normal
    exact ⟨valid,Frame.of_readonly pure⟩
  · rw [long_string_shape] at normal
    have difference : byte-183#64=BitVec.ofNat 64 (byte.toNat-183) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 183 (by decide) (by omega)
    obtain ⟨valid,frame,pure,kind⟩ := long_case_normal source post pointer length byte 183#64 0#64 (byte.toNat-183) entry (by omega) difference (Or.inl rfl) byteCell installed value normal
    exact ⟨valid,frame⟩
  · obtain ⟨valid,frame,kind⟩ := short_list_normal source post pointer length byte entry byteCell installed value normal
    exact ⟨valid,frame⟩
  · rw [long_list_shape] at normal
    have difference : byte-247#64=BitVec.ofNat 64 (byte.toNat-247) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 247 (by decide) (by omega)
    obtain ⟨valid,frame,pure,kind⟩ := long_case_normal source post pointer length byte 247#64 1#64 (byte.toNat-247) entry (by omega) difference (Or.inr rfl) byteCell installed value normal
    exact ⟨valid,frame⟩

/-- The real original item decoder derives its actual four-word result,
binary kind, nonwrapping payload/total extent and retained arena. No decoded
item, callee output or future memory model is assumed. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Input.CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Frame source post ∧ source.clock-post.clock≤60*length.toNat+10 := by
  have priced := body_cost source pointer length pointerCell lengthCell arena fits installed
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
  have entry : Entry source pointer length := ⟨pointerCell,lengthCell,arena,positive,fits⟩
  have nextEntry : Entry entered pointer length := Entry.bound_word source pointer length byte "b" entry (by decide) (by decide)
  obtain ⟨valid,nextArena⟩ := after_byte_normal entered inner pointer length byte nextEntry small (bind_lookup_same _ _ _) installed value innerRun
  refine ⟨valid,?_,priced⟩
  · rw [restored]
    exact nextArena.of_erase rfl rfl

/-- A real returned string cannot have taken a list branch. Its actual
short/long string path is readonly, including its length-reader prefix. -/
theorem after_byte_string_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length byte : BitVec 64) (entry : Entry source pointer length)
    (byteSmall : byte.toNat<256) (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (stringKind : kindOf value=some 0#64)
    (normal : evaluateHOLFiniteState source afterByte=(some (.returned value),post)) :
    Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  rw [after_byte_evaluate source byte byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · exact (single_normal source post pointer length entry value normal).2
  · exact (short_string_normal source post pointer length byte entry byteCell installed value normal).2
  · rw [long_string_shape] at normal
    have difference : byte-183#64=BitVec.ofNat 64 (byte.toNat-183) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 183 (by decide) (by omega)
    obtain ⟨valid,frame,pure,kind⟩ := long_case_normal source post pointer length byte 183#64 0#64 (byte.toNat-183) entry (by omega) difference (Or.inl rfl) byteCell installed value normal
    exact pure rfl
  · obtain ⟨valid,frame,kind⟩ := short_list_normal source post pointer length byte entry byteCell installed value normal
    exact ((by decide : (some (1#64 : BitVec 64))≠some 0#64) (kind.symm.trans stringKind)).elim
  · rw [long_list_shape] at normal
    have difference : byte-247#64=BitVec.ofNat 64 (byte.toNat-247) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w:=64) byte.toNat 247 (by decide) (by omega)
    obtain ⟨valid,frame,pure,kind⟩ := long_case_normal source post pointer length byte 247#64 1#64 (byte.toNat-247) entry (by omega) difference (Or.inr rfl) byteCell installed value normal
    exact ((by decide : (some (1#64 : BitVec 64))≠some 0#64) (kind.symm.trans stringKind)).elim

/-- The actual item caller's string result restores the whole nonlocal state;
this stronger result is used only after a real string result is derived. -/
theorem body_string_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Input.CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (stringKind : kindOf value=some 0#64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
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
  have entry : Entry source pointer length := ⟨pointerCell,lengthCell,arena,positive,fits⟩
  have nextEntry : Entry entered pointer length := Entry.bound_word source pointer length byte "b" entry (by decide) (by decide)
  have pure := after_byte_string_frame entered inner pointer length byte nextEntry small (bind_lookup_same _ _ _) installed value stringKind innerRun
  rw [restored]
  exact pure

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_byte_normal
#print axioms InitECandidate.Solver.Rlp.CurrentItem.body_normal

#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_byte_string_frame
#print axioms InitECandidate.Solver.Rlp.CurrentItem.body_string_frame
