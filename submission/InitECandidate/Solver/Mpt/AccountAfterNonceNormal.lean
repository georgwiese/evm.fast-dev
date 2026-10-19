import InitECandidate.Solver.Mpt.AccountBalancePhaseNormal
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal nonce store and balance guard derive the32-byte balance
limit, then compose the entire original balance/reference output phase. -/
theorem after_nonce_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out nonce pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (nonceCell : source.locals.lookup (ofString "nonce")=some (.val (.word nonce)))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (cell2 : source.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2))
    (cell3 : source.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterNonce=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ payload1.toNat≤32 ∧ (payload2=0#64 ∨ payload2=32#64) ∧ (payload3=0#64 ∨ payload3=32#64) ∧
      Rlp.Slices.Window source post out.toNat (out.toNat+56) ∧
      post.memory (out+40#64)=.word (if payload2=0#64 then emptyRoot else pointer2+header2) ∧
      post.memory (out+48#64)=.word (if payload3=0#64 then emptyHash else pointer3+header3) := by
  rw [after_nonce_shape] at normal
  obtain ⟨stored,storeRun,guardTail,locals⟩ := (Input.LocalPrefix.store (key:=ofString "acct_out") _ _).normal_continue source post
    (.seq (.ite (.cmp .lower (.const 32#64) (field "f1" 2)) (fail 22#64) .skip) balancePhase) returned normal
  have addressRead : eval source (.op .add [localVar "acct_out",.const 0#64])=some (.val (.word out)) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,outputCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have nonceRead : eval source (localVar "nonce")=some (.val (.word nonce)) := by simp [eval,evalHOLExact,localVar,toExact,nonceCell]
  obtain ⟨mapped,storedEq⟩ := Input.word_store_normal source stored _ _ out nonce addressRead nonceRead storeRun
  have nextOutput : stored.locals.lookup (ofString "acct_out")=some (.val (.word out)) := by rw [storedEq]; exact outputCell
  have next1 : stored.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1) := by rw [storedEq]; exact cell1
  have next2 : stored.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2) := by rw [storedEq]; exact cell2
  have next3 : stored.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3) := by rw [storedEq]; exact cell3
  have nextRoot : stored.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by rw [storedEq]; exact rootGlobal
  have nextHash : stored.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)) := by rw [storedEq]; exact hashGlobal
  have nextDomain : stored.memaddrs=InitE.ordinaryDomain := by rw [storedEq]; exact domain
  have nextInstalled : Input.OriginalCode.Installed stored.code := by rw [storedEq]; exact installed
  have guardSafe : Input.LocalPrefix (ofString "acct_out") (.ite (.cmp .lower (.const 32#64) (field "f1" 2)) (fail 22#64) .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨guardPost,guardRun,phaseRun,localEq⟩ := guardSafe.normal_continue stored post balancePhase returned guardTail
  have guardEq := (Fail.guard_normal stored guardPost _ [.const 22#64] nextInstalled guardRun).2
  subst guardPost
  have small := Fail.lower_guard_bound stored stored (.const 32#64) (field "f1" 2) 32#64 payload1 [.const 22#64] rfl
    (payload_read stored "f1" pointer1 header1 payload1 flag1 next1) nextInstalled guardRun
  obtain ⟨result,rootWidth,hashWidth,phaseWindow,root,hash⟩ := balance_phase_normal stored post out pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash
    nextOutput next1 next2 next3 nextRoot nextHash output nextDomain small nextInstalled returned phaseRun
  have storeWindow : Rlp.Slices.Window source stored out.toNat (out.toNat+56) := by
    intro query outside
    rw [storedEq]
    have different : query≠out := by simpa only [BitVec.add_zero] using output.outside_address out 0 (by decide) query outside
    simp only [StoreWord.put,if_neg different]
  exact ⟨result,small,rootWidth,hashWidth,Rlp.Slices.Window.trans source stored post _ _ storeWindow phaseWindow,root,hash⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_nonce_normal
