import InitECandidate.Solver.Mpt.AccountAfterNonceNormal
import InitECandidate.Solver.Mpt.AccountNonceScalar
import InitECandidate.Solver.Mpt.AccountDecodeTailGlobals
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual accumulator/index declarations and entire nonce loop feed
the real scalar nonce store. All input field bindings and globals used by
the balance/reference phase survive, with no supplied future loop state. -/
theorem nonce_setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (cell2 : source.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2))
    (cell3 : source.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source nonceSetup=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ payload1.toNat≤32 ∧ (payload2=0#64 ∨ payload2=32#64) ∧ (payload3=0#64 ∨ payload3=32#64) ∧
      Rlp.Slices.Window source post out.toNat (out.toNat+56) ∧
      post.memory (out+40#64)=.word (if payload2=0#64 then emptyRoot else pointer2+header2) ∧
      post.memory (out+48#64)=.word (if payload3=0#64 then emptyHash else pointer3+header3) := by
  rw [nonceSetup] at normal
  obtain ⟨innerNonce,nonceRun,restoreNonce⟩ := Input.declaration_return_word source post "nonce" (.const 0#64) 0#64 _ returned rfl normal
  let declared := bind source "nonce" 0#64
  obtain ⟨innerIndex,indexRun,restoreIndex⟩ := Input.declaration_return_word declared innerNonce "i" (.const 0#64) 0#64 _ returned rfl nonceRun
  let entered := bind declared "i" 0#64
  have setupCell (name : String) (notNonce : ofString "nonce"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      entered.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other declared "i" name 0#64 notIndex).trans (bind_lookup_other source "nonce" name 0#64 notNonce)
  have safe (name : String) (notNonce : ofString name≠ofString "nonce") (notIndex : ofString name≠ofString "i") :
      Input.LocalPrefix (ofString name) nonceLoop := by
    rw [nonce_loop_shape,nonce_body_shape]
    exact .loop _ (.seq (.assign _ _ notNonce) (.assign _ _ notIndex))
  obtain ⟨noncePost,loopRun,tailRun,outputEq⟩ := (safe "acct_out" (by decide) (by decide)).normal_continue entered innerIndex afterNonce returned indexRun
  have initialNonce : entered.locals.lookup (ofString "nonce")=some (.val (.word 0#64)) :=
    (bind_lookup_other declared "i" "nonce" 0#64 (by decide)).trans (bind_lookup_same source "nonce" 0#64)
  obtain ⟨nonce,nonceCell⟩ := nonce_loop_scalar entered noncePost 0#64 initialNonce loopRun
  have saved (name : String) (notNonce : ofString name≠ofString "nonce") (notIndex : ofString name≠ofString "i") :
      noncePost.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (safe name notNonce notIndex).summary_full entered
    unfold Input.LocalSummary at summary
    rw [loopRun] at summary
    exact (summary.1 rfl).trans (setupCell name (Ne.symm notNonce) (Ne.symm notIndex))
  have nextOutput := (saved "acct_out" (by decide) (by decide)).trans outputCell
  have next1 := (saved "f1" (by decide) (by decide)).trans cell1
  have next2 := (saved "f2" (by decide) (by decide)).trans cell2
  have next3 := (saved "f3" (by decide) (by decide)).trans cell3
  have frame := nonce_loop_readonly entered.code entered rfl
  rw [loopRun] at frame
  have memory : noncePost.memory=source.memory := Input.LocalEffects.memory_of_erase entered noncePost frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change noncePost.globals=source.globals at globals
  have domains := congrArg PanSemStateFiniteExact.memaddrs frame
  change noncePost.memaddrs=source.memaddrs at domains
  have codes := congrArg PanSemStateFiniteExact.code frame
  change noncePost.code=source.code at codes
  have nextRoot : noncePost.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by rw [globals]; exact rootGlobal
  have nextHash : noncePost.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)) := by rw [globals]; exact hashGlobal
  have nextInstalled : Input.OriginalCode.Installed noncePost.code := by rw [codes]; exact installed
  obtain ⟨result,small,rootWidth,hashWidth,window,root,hash⟩ := after_nonce_normal noncePost innerIndex out nonce pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash
    nextOutput nonceCell next1 next2 next3 nextRoot nextHash output (domains.trans domain) nextInstalled returned tailRun
  refine ⟨result,small,rootWidth,hashWidth,?_,?_,?_⟩
  · intro query outside
    rw [restoreNonce,restoreIndex]
    change innerIndex.memory query=source.memory query
    exact (window query outside).trans (congrFun memory query)
  · rw [restoreNonce,restoreIndex]
    exact root
  · rw [restoreNonce,restoreIndex]
    exact hash

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_setup_normal
