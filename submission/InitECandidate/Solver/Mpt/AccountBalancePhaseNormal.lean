import InitECandidate.Solver.Mpt.AccountBalanceLoopFrame
import InitECandidate.Solver.Mpt.AccountClearFrame
import InitECandidate.Solver.Mpt.AccountAfterBalanceNormal
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete actual original balance phase: real clear, reset, whole byte
loop and final references. It returns0 and writes only the account object,
with actual root/hash word values and derived0/32 reference widths. -/
theorem balance_phase_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (cell2 : source.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2))
    (cell3 : source.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (small : payload1.toNat≤32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source balancePhase=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ (payload2=0#64 ∨ payload2=32#64) ∧ (payload3=0#64 ∨ payload3=32#64) ∧
      Rlp.Slices.Window source post out.toNat (out.toNat+56) ∧
      post.memory (out+40#64)=.word (if payload2=0#64 then emptyRoot else pointer2+header2) ∧
      post.memory (out+48#64)=.word (if payload3=0#64 then emptyHash else pointer3+header3) := by
  rw [balance_phase_shape] at normal
  have clearSafe : Input.LocalPrefix (ofString "acct_out") clearCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨cleared,clearRun,resetTail,outputEq⟩ := clearSafe.normal_continue source post
    (.seq (.assign .local (ofString "i") (.const 0#64)) (.seq balanceLoop afterBalance)) returned normal
  obtain ⟨positive,clearEq⟩ := clear_none source cleared out outputCell output domain installed clearRun
  have resetSafe : Input.LocalPrefix (ofString "acct_out") (.assign .local (ofString "i") (.const 0#64)) := .assign _ _ (by decide)
  obtain ⟨reset,resetRun,loopTail,resetOutputEq⟩ := resetSafe.normal_continue cleared post (.seq balanceLoop afterBalance) returned resetTail
  have resetEq := Input.assign_none cleared reset "i" (.const 0#64) 0#64 rfl resetRun
  rw [resetEq] at loopTail
  let entered := bind cleared "i" 0#64
  have currentCell (name : String) (other : ofString "i"≠ofString name) :
      entered.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other cleared "i" name 0#64 other).trans (by rw [clearEq])
  have enteredOut := (currentCell "acct_out" (by decide)).trans outputCell
  have entered1 := (currentCell "f1" (by decide)).trans cell1
  have entered2 := (currentCell "f2" (by decide)).trans cell2
  have entered3 := (currentCell "f3" (by decide)).trans cell3
  have enteredRoot : entered.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by change cleared.globals.lookup _=_; rw [clearEq]; exact rootGlobal
  have enteredHash : entered.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)) := by change cleared.globals.lookup _=_; rw [clearEq]; exact hashGlobal
  have enteredInstalled : Input.OriginalCode.Installed entered.code := by change Input.OriginalCode.Installed cleared.code; rw [clearEq]; exact installed
  have loopSafe : Input.LocalPrefix (ofString "acct_out") balanceLoop := by rw [balance_loop_shape]; exact .loop _ balance_body_output_safe
  obtain ⟨loopPost,loopRun,referenceRun,loopOutputEq⟩ := loopSafe.normal_continue entered post afterBalance returned loopTail
  have loop2 := (balance_loop_saved entered loopPost "f2" (by decide) (by decide) (by decide) loopRun).trans entered2
  have loop3 := (balance_loop_saved entered loopPost "f3" (by decide) (by decide) (by decide) loopRun).trans entered3
  have loopOut := loopOutputEq.trans enteredOut
  have rootFrame := balance_loop_globals (ofString "empty_trie_root") entered.code entered rfl
  have hashFrame := balance_loop_globals (ofString "empty_code_hash") entered.code entered rfl
  rw [loopRun] at rootFrame hashFrame
  have loopRoot := (congrArg Prod.snd rootFrame).trans enteredRoot
  have loopHash := (congrArg Prod.snd hashFrame).trans enteredHash
  have loopInstalled := Input.OriginalCode.after_execution entered loopPost balanceLoop none loopRun enteredInstalled
  obtain ⟨returnedEq,rootWidth,hashWidth,referenceEq⟩ := after_balance_normal loopPost post out pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash
    loopOut loop2 loop3 loopRoot loopHash loopInstalled returned referenceRun
  have firstWindow := clear_window source cleared out outputCell output domain installed clearRun
  have entryWindow : Rlp.Slices.Window source entered out.toNat (out.toNat+56) := firstWindow
  have loopWindow := balance_loop_window entered loopPost out pointer1 header1 payload1 flag1 0#64 enteredOut entered1 (bind_lookup_same _ _ _) output small (by simp) loopRun
  have referenceWindow : Rlp.Slices.Window loopPost post out.toNat (out.toNat+56) := by
    rw [referenceEq]
    exact output.references_window loopPost out _ _
  have window := Rlp.Slices.Window.trans source entered post out.toNat (out.toNat+56) entryWindow
    (Rlp.Slices.Window.trans entered loopPost post out.toNat (out.toNat+56) loopWindow referenceWindow)
  have different : out+40#64≠out+48#64 := byteAddress_ne out 40 48 (by have := output.upper; omega) (by have := output.upper; omega) (by decide)
  refine ⟨returnedEq,rootWidth,hashWidth,window,?_,?_⟩
  · rw [referenceEq]
    change StoreWord.put (StoreWord.put loopPost.memory (out+40#64) _) (out+48#64) _ (out+40#64)=_
    simp [StoreWord.put,different]
  · rw [referenceEq]
    change StoreWord.put (StoreWord.put loopPost.memory (out+40#64) _) (out+48#64) _ (out+48#64)=_
    simp [StoreWord.put]

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_phase_normal
