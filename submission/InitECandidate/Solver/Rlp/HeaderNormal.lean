import InitECandidate.Solver.Rlp.HeaderLongValues
import InitECandidate.Solver.Rlp.HeaderCall
import InitECandidate.Solver.Input.ByteExpressionBound
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

theorem after_byte_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte length : BitVec 64)
    (byteSmall : byte.toNat<256) (positive : 0<length.toNat)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) : Returns source afterByte (Valid length.toNat) := by
  intro post returned normal
  rw [after_byte_evaluate source byte byteCell] at normal
  split_ifs at normal with singleCase shortStringCase longStringCase shortListCase
  · exact single_returns source length positive post returned normal
  · exact short_string_returns source byte length positive byteCell lengthCell installed post returned normal
  · rw [long_string_shape] at normal
    have difference : byte-183#64=BitVec.ofNat 64 (byte.toNat-183) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w := 64) byte.toNat 183 (by decide) (by omega)
    exact long_case_returns source byte length 183#64 0#64 (byte.toNat-183) positive (by omega) difference (Or.inl rfl)
      byteCell lengthCell installed post returned normal
  · exact short_list_returns source byte length positive byteCell lengthCell installed post returned normal
  · rw [long_list_shape] at normal
    have difference : byte-247#64=BitVec.ofNat 64 (byte.toNat-247) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using BitVec.ofNat_sub_ofNat_of_le (w := 64) byte.toNat 247 (by decide) (by omega)
    exact long_case_returns source byte length 247#64 1#64 (byte.toNat-247) positive (by omega) difference (Or.inr rfl)
      byteCell lengthCell installed post returned normal

/-- The original decoder's actual normal return derives its positive,
nonwrapping item size inside the current input length and binary list flag.
The initial empty-input guard and actual first-byte read are inverted here. -/
theorem body_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) : Returns source body (Valid length.toNat) := by
  intro post returned normal
  rw [body_shape] at normal
  have lengthRead : eval source (localVar "len")=some (.val (.word length)) := by simp [eval,localVar,evalHOLExact,toExact,lengthCell]
  obtain ⟨nonzero,byteRun⟩ := Fail.equal_guard_return source post (localVar "len") (.const 0#64) length 0#64 [.const 1#64] afterGuard returned lengthRead rfl installed normal
  have positive : 0<length.toNat := by
    by_contra zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change length.toNat=0
    omega
  rw [byte_shape] at byteRun
  obtain ⟨declared,inner,byteRead,typed,innerRun,restored⟩ :=
    Input.CallNormal.declaration_normal_entry source post "b" .one (.loadByte (localVar "p")) afterByte returned byteRun
  obtain ⟨byte,byteEq,small⟩ := Input.byte_expression_value source (localVar "p") declared byteRead
  rw [byteEq] at innerRun
  let entered := bind source "b" byte
  have currentByte : entered.locals.lookup (ofString "b")=some (.val (.word byte)) := bind_lookup_same _ _ _
  have currentLength : entered.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "b" "len" byte (by decide)).trans lengthCell
  exact after_byte_returns entered byte length small positive currentByte currentLength installed inner returned innerRun

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    Valid length.toNat returned ∧ post.clock≤source.clock ∧ source.clock-10≤post.clock ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  have answer := body_returns source length lengthCell installed post returned normal
  have cost := body_cost source pointer pointerCell installed
  have clock := evaluateHOLFiniteState_clock_le source body
  have fields := readonly source.code installed source rfl
  rw [normal] at cost clock fields
  exact ⟨answer,clock,by change source.clock-post.clock≤10 at cost; omega,fields⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.after_byte_returns
#print axioms InitECandidate.Solver.Rlp.Header.body_returns
#print axioms InitECandidate.Solver.Rlp.Header.body_normal
