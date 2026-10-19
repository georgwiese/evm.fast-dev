import InitECandidate.Solver.Rlp.UncheckedLongObservation

namespace InitECandidate.Solver.Rlp.Unchecked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_byte_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (loaded : UInt8)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 loaded.toNat))))
    (byteRead : ReadLength.byte source pointer=some loaded)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterByte=(some (.returned value),post)) :
    ∃ header payload flag : BitVec 64,Header.Encoded source pointer header payload flag ∧ value=.val (.word (header+payload)) := by
  rw [after_byte_evaluate source (BitVec.ofNat 64 loaded.toNat) byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · rw [single_shape] at normal
    have actual := (Input.return_normal source post _ value normal).1
    have answer : value=.val (.word 1#64) := by simpa only [eval,evalHOLExact,Option.some.injEq] using actual.symm
    refine ⟨0#64,1#64,0#64,⟨loaded,byteRead,?_⟩,?_⟩
    · simp only [if_pos singleCase]; trivial
    · simpa using answer
  · rw [short_string_shape] at normal
    have expected : eval source (.op .sub [.op .add [.const 1#64,localVar "b"],.const 128#64])=
        some (.val (.word (1#64+(BitVec.ofNat 64 loaded.toNat-128#64)))) := by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    have actual := (Input.return_normal source post _ value normal).1
    exact ⟨1#64,BitVec.ofNat 64 loaded.toNat-128#64,0#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_pos shortStringCase]; trivial⟩,
      Option.some.inj (actual.symm.trans expected)⟩
  · rw [long_string_shape] at normal
    obtain ⟨payload,observed,answer⟩ := long_case_observed source post pointer (BitVec.ofNat 64 loaded.toNat) 183#64 "ll" "n"
      (by decide) (by decide) pointerCell byteCell installed value normal
    exact ⟨1#64+(BitVec.ofNat 64 loaded.toNat-183#64),payload,0#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_pos longStringCase]; exact ⟨True.intro,True.intro,observed⟩⟩,answer⟩
  · rw [short_list_shape] at normal
    have expected : eval source (.op .sub [.op .add [.const 1#64,localVar "b"],.const 192#64])=
        some (.val (.word (1#64+(BitVec.ofNat 64 loaded.toNat-192#64)))) := by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    have actual := (Input.return_normal source post _ value normal).1
    exact ⟨1#64,BitVec.ofNat 64 loaded.toNat-192#64,1#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_neg longStringCase,if_pos shortListCase]; trivial⟩,
      Option.some.inj (actual.symm.trans expected)⟩
  · rw [long_list_shape] at normal
    obtain ⟨payload,observed,answer⟩ := long_case_observed source post pointer (BitVec.ofNat 64 loaded.toNat) 247#64 "ll2" "n2"
      (by decide) (by decide) pointerCell byteCell installed value normal
    exact ⟨1#64+(BitVec.ofNat 64 loaded.toNat-247#64),payload,1#64,
      ⟨loaded,byteRead,by simp only [if_neg singleCase,if_neg shortStringCase,if_neg longStringCase,if_neg shortListCase]; exact ⟨True.intro,True.intro,observed⟩⟩,answer⟩

/-- The actual unchecked return records its real input byte, original
length-reader observation and arithmetic total. No validation or expected
decoded size is a premise. -/
theorem body_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header payload flag : BitVec 64,Header.Encoded source pointer header payload flag ∧ value=.val (.word (header+payload)) := by
  classical
  rw [body_shape] at normal
  cases byteRead : ReadLength.byte source pointer with
  | none =>
    have read : eval source (.loadByte (localVar "p"))=none := by
      simpa [eval,evalHOLExact,localVar,toExact,pointerCell,ReadLength.byte] using
        congrArg (Option.map (fun b : UInt8=>ValueHOL.val (.word (BitVec.ofNat 64 b.toNat)))) byteRead
    simp only [eval] at read
    rw [evaluateHOLFiniteState_dec_total] at normal
    dsimp only at normal
    rw [read] at normal
    cases normal
  | some loaded =>
    have read : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 loaded.toNat))) := by
      simpa [eval,evalHOLExact,localVar,toExact,pointerCell,ReadLength.byte] using
        congrArg (Option.map (fun b : UInt8=>ValueHOL.val (.word (BitVec.ofNat 64 b.toNat)))) byteRead
    obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "b" _ (BitVec.ofNat 64 loaded.toNat) afterByte value read normal
    let entered := bind source "b" (BitVec.ofNat 64 loaded.toNat)
    have enteredPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
      (bind_lookup_other _ "b" "p" _ (by decide)).trans pointerCell
    exact after_byte_encoding entered inner pointer loaded enteredPointer (bind_lookup_same _ _ _) byteRead installed value innerRun

end InitECandidate.Solver.Rlp.Unchecked

#print axioms InitECandidate.Solver.Rlp.Unchecked.after_byte_encoding
#print axioms InitECandidate.Solver.Rlp.Unchecked.body_encoding
