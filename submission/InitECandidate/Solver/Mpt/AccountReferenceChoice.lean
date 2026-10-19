import InitECandidate.Solver.Mpt.AccountDecodeOutput
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.CompareZero
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def referenceChoice (name : String) (offset : Nat) (emptyName : String) (error : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (field name 2) (.const 0#64))
    (.store (.op .add [localVar "acct_out",.const (BitVec.ofNat 64 offset)]) (.var .global (ofString emptyName)))
    (.seq (.ite (.cmp .notEqual (field name 2) (.const 32#64)) (fail error) .skip)
      (.store (.op .add [localVar "acct_out",.const (BitVec.ofNat 64 offset)]) (field name 1)))

theorem after_balance_reference_shape : afterBalance=.seq (referenceChoice "f2" 40 "empty_trie_root" 23#64)
    (.seq (referenceChoice "f3" 48 "empty_code_hash" 24#64) (.return (.const 0#64))) := by
  rw [after_balance_shape]
  rfl

theorem reference_choice_safe (key : MlS) (name : String) (offset : Nat) (emptyName : String) (error : BitVec 64) :
    Input.LocalPrefix key (referenceChoice name offset emptyName error) :=
  .ite _ (.store _ _) (.seq (.ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip) (.store _ _))

/-- The real zero-or32 guard derives the stored reference, exact single
word effect and width restriction from an actual normal outcome. -/
theorem reference_choice_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag empty : BitVec 64) (name emptyName : String) (offset : Nat) (error : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (fieldCell : source.locals.lookup (ofString name)=some (Rlp.Item.result pointer header payload flag))
    (emptyCell : source.globals.lookup (ofString emptyName)=some (.val (.word empty)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (referenceChoice name offset emptyName error)=(none,post)) :
    (payload=0#64 ∨ payload=32#64) ∧
      post={source with memory:=StoreWord.put source.memory (out+BitVec.ofNat 64 offset) (if payload=0#64 then empty else pointer+header)} := by
  have addressRead : eval source (.op .add [localVar "acct_out",.const (BitVec.ofNat 64 offset)])=some (.val (.word (out+BitVec.ofNat 64 offset))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,outputCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  by_cases zero : payload=0#64
  · have chosen : evaluateHOLFiniteState source (referenceChoice name offset emptyName error)=
        evaluateHOLFiniteState source (.store (.op .add [localVar "acct_out",.const (BitVec.ofNat 64 offset)]) (.var .global (ofString emptyName))) := by
      rw [referenceChoice,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,fieldCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [chosen] at normal
    have emptyRead : eval source (.var .global (ofString emptyName))=some (.val (.word empty)) := by simp [eval,evalHOLExact,toExact,emptyCell]
    obtain ⟨mapped,same⟩ := Input.word_store_normal source post _ _ (out+BitVec.ofNat 64 offset) empty addressRead emptyRead normal
    exact ⟨Or.inl zero,by simpa only [if_pos zero] using same⟩
  · have chosen : evaluateHOLFiniteState source (referenceChoice name offset emptyName error)=
        evaluateHOLFiniteState source (.seq (.ite (.cmp .notEqual (field name 2) (.const 32#64)) (fail error) .skip)
          (.store (.op .add [localVar "acct_out",.const (BitVec.ofNat 64 offset)]) (field name 1))) := by
      rw [referenceChoice,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,fieldCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [chosen] at normal
    obtain ⟨middle,guardRun,storeRun⟩ := Input.sequence_none source post _ _ normal
    obtain ⟨passed,middleEq⟩ := Fail.guard_normal source middle _ [.const error] installed guardRun
    subst middle
    have payloadRead := payload_read source name pointer header payload flag fieldCell
    have width := Input.CompareFacts.not_equal_zero source (field name 2) (.const 32#64) payload 32#64 payloadRead rfl passed
    have pointerRead : eval source (field name 1)=some (.val (.word (pointer+header))) := by
      simp [field,eval,evalHOLExact,localVar,toExact,fieldCell,Rlp.Item.result]
    obtain ⟨mapped,same⟩ := Input.word_store_normal source post _ _ (out+BitVec.ofNat 64 offset) (pointer+header) addressRead pointerRead storeRun
    exact ⟨Or.inr width,by simpa only [if_neg zero] using same⟩

theorem Output.outside_address (out : BitVec 64) (output : Output out) (offset : Nat) (inside : offset<56)
    (query : BitVec 64) (outside : query.toNat<out.toNat ∨ out.toNat+56≤query.toNat) : query≠out+BitVec.ofNat 64 offset := by
  have offsetSmall : offset<2^64 := by omega
  have number : (out+BitVec.ofNat 64 offset).toNat=out.toNat+offset := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]; have := output.upper; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  intro equal
  have arithmetic := congrArg BitVec.toNat equal
  rw [number] at arithmetic
  rcases outside with before|after <;> omega

theorem reference_choice_window (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag empty : BitVec 64) (name emptyName : String) (offset : Nat) (error : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (fieldCell : source.locals.lookup (ofString name)=some (Rlp.Item.result pointer header payload flag))
    (emptyCell : source.globals.lookup (ofString emptyName)=some (.val (.word empty)))
    (output : Output out) (inside : offset<56) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (referenceChoice name offset emptyName error)=(none,post)) :
    Rlp.Slices.Window source post out.toNat (out.toNat+56) := by
  obtain ⟨width,same⟩ := reference_choice_normal source post out pointer header payload flag empty name emptyName offset error outputCell fieldCell emptyCell installed normal
  intro query outside
  rw [same]
  change StoreWord.put source.memory (out+BitVec.ofNat 64 offset) _ query=source.memory query
  simp only [StoreWord.put,if_neg (output.outside_address out offset inside query outside)]

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_balance_reference_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.reference_choice_safe
#print axioms InitECandidate.Solver.Mpt.AccountDecode.reference_choice_normal
#print axioms InitECandidate.Solver.Mpt.AccountDecode.reference_choice_window

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.outside_address
