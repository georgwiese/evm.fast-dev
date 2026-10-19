import InitECandidate.Solver.Rlp.HeaderLongEncoding
import InitECandidate.Solver.Rlp.HeaderShortEncoding
import InitECandidate.Solver.Rlp.HeaderControl

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (loaded : UInt8)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 loaded.toNat))))
    (byteRead : ReadLength.byte source pointer=some loaded)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterByte=(some (.returned value),post)) :
    ∃ header payload flag : BitVec 64,Encoded source pointer header payload flag ∧ value=result header payload flag := by
  rw [after_byte_evaluate source (BitVec.ofNat 64 loaded.toNat) byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · rw [single_shape] at normal
    have expected : eval source (.rstruct [.const 0#64,.const 1#64,.const 0#64])=some (result 0#64 1#64 0#64) := by
      simp [eval,evalHOLExact,evalListHOLExact,result]
    have actual := (Input.return_normal source post _ value normal).1
    exact ⟨0#64,1#64,0#64,⟨loaded,byteRead,by simp only [if_pos singleCase]; trivial⟩,
      Option.some.inj (actual.symm.trans expected)⟩
  · have answer := short_string_encoding source post (BitVec.ofNat 64 loaded.toNat) byteCell installed value normal
    exact ⟨1#64,BitVec.ofNat 64 loaded.toNat-128#64,0#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_pos shortStringCase]; trivial⟩,answer⟩
  · rw [long_string_shape] at normal
    obtain ⟨payload,observed,answer⟩ := long_case_encoding source post pointer (BitVec.ofNat 64 loaded.toNat) 183#64 0#64
      pointerCell byteCell installed value normal
    exact ⟨1#64+(BitVec.ofNat 64 loaded.toNat-183#64),payload,0#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_pos longStringCase]; exact ⟨True.intro,True.intro,observed⟩⟩,answer⟩
  · have answer := short_list_encoding source post (BitVec.ofNat 64 loaded.toNat) byteCell installed value normal
    exact ⟨1#64,BitVec.ofNat 64 loaded.toNat-192#64,1#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_neg longStringCase,if_pos shortListCase]; trivial⟩,answer⟩
  · rw [long_list_shape] at normal
    obtain ⟨payload,observed,answer⟩ := long_case_encoding source post pointer (BitVec.ofNat 64 loaded.toNat) 247#64 1#64
      pointerCell byteCell installed value normal
    exact ⟨1#64+(BitVec.ofNat 64 loaded.toNat-247#64),payload,1#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_neg longStringCase,if_neg shortListCase]; exact ⟨True.intro,True.intro,observed⟩⟩,answer⟩

/-- Actual successful validation records the first byte and any actual
length-reader result, for comparison with the original unchecked pass. -/
theorem body_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header payload flag : BitVec 64,Encoded source pointer header payload flag ∧ value=result header payload flag := by
  classical
  rw [body_shape] at normal
  obtain ⟨guardRun,byteRun⟩ := Fail.guard_return source post (.cmp .equal (localVar "len") (.const 0#64)) [.const 1#64] afterGuard value installed normal
  rw [byte_shape] at byteRun
  cases byteRead : ReadLength.byte source pointer with
  | none =>
    have read : eval source (.loadByte (localVar "p"))=none := by
      simpa [eval,evalHOLExact,localVar,toExact,pointerCell,ReadLength.byte] using
        congrArg (Option.map (fun b : UInt8=>ValueHOL.val (.word (BitVec.ofNat 64 b.toNat)))) byteRead
    simp only [eval] at read
    rw [evaluateHOLFiniteState_dec_total] at byteRun
    dsimp only at byteRun
    rw [read] at byteRun
    cases byteRun
  | some loaded =>
    have read : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 loaded.toNat))) := by
      simpa [eval,evalHOLExact,localVar,toExact,pointerCell,ReadLength.byte] using
        congrArg (Option.map (fun b : UInt8=>ValueHOL.val (.word (BitVec.ofNat 64 b.toNat)))) byteRead
    obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "b" _ (BitVec.ofNat 64 loaded.toNat) afterByte value read byteRun
    let entered := bind source "b" (BitVec.ofNat 64 loaded.toNat)
    have enteredPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
      (bind_lookup_other _ "b" "p" _ (by decide)).trans pointerCell
    exact after_byte_encoding entered inner pointer loaded enteredPointer (bind_lookup_same _ _ _) byteRead installed value innerRun

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.after_byte_encoding
#print axioms InitECandidate.Solver.Rlp.Header.body_encoding
