import InitECandidate.Solver.Mpt.AccountNonceSetupNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Complete actual normal original output suffix. Its real guards derive
four string flags, nonce<=8, balance<=32 and root/hash0-or32 widths. Both
byte loops and every output write preserve all words outside the account. -/
theorem after_fields_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (cell2 : source.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2))
    (cell3 : source.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterFields=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ (flag0=0#64 ∧ flag1=0#64 ∧ flag2=0#64 ∧ flag3=0#64) ∧
      payload0.toNat≤8 ∧ payload1.toNat≤32 ∧ (payload2=0#64 ∨ payload2=32#64) ∧ (payload3=0#64 ∨ payload3=32#64) ∧
      Rlp.Slices.Window source post out.toNat (out.toNat+56) ∧
      post.memory (out+40#64)=.word (if payload2=0#64 then emptyRoot else pointer2+header2) ∧
      post.memory (out+48#64)=.word (if payload3=0#64 then emptyHash else pointer3+header3) := by
  let flags : ExpHOL 64 := .op .or [field "f0" 0,field "f1" 0,field "f2" 0,field "f3" 0]
  rw [after_fields_shape] at normal
  change evaluateHOLFiniteState source (.seq (.ite (.cmp .notEqual flags (.const 0#64)) (fail 20#64) .skip)
    (.seq (.ite (.cmp .lower (.const 8#64) (field "f0" 2)) (fail 21#64) .skip) nonceSetup))=(some (.returned returned),post) at normal
  have flagsSafe : Input.LocalPrefix (ofString "acct_out") (.ite (.cmp .notEqual flags (.const 0#64)) (fail 20#64) .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨flagsPost,flagsRun,nonceGuardRun,locals⟩ := flagsSafe.normal_continue source post
    (.seq (.ite (.cmp .lower (.const 8#64) (field "f0" 2)) (fail 21#64) .skip) nonceSetup) returned normal
  obtain ⟨flagsPassed,flagsEq⟩ := Fail.guard_normal source flagsPost _ [.const 20#64] installed flagsRun
  subst flagsPost
  have flagsRead : eval source flags=some (.val (.word (flag0 ||| (flag1 ||| (flag2 ||| flag3))))) := by
    simp [flags,field,eval,evalHOLExact,evalListHOLExact,localVar,toExact,cell0,cell1,cell2,cell3,Rlp.Item.result,valueIsWord,valueWord,wordOpHOL,wordOp,OrOp.or]
  have zeroFlags := Input.CompareFacts.not_equal_zero source flags (.const 0#64) (flag0 ||| (flag1 ||| (flag2 ||| flag3))) 0#64 flagsRead rfl flagsPassed
  have stringFlags : flag0=0#64 ∧ flag1=0#64 ∧ flag2=0#64 ∧ flag3=0#64 := by
    simpa only [BitVec.or_eq_zero_iff] using zeroFlags
  have guardSafe : Input.LocalPrefix (ofString "acct_out") (.ite (.cmp .lower (.const 8#64) (field "f0" 2)) (fail 21#64) .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨guardPost,guardRun,setupRun,outputEq⟩ := guardSafe.normal_continue source post nonceSetup returned nonceGuardRun
  have guardEq := (Fail.guard_normal source guardPost _ [.const 21#64] installed guardRun).2
  subst guardPost
  have nonceBound := Fail.lower_guard_bound source source (.const 8#64) (field "f0" 2) 8#64 payload0 [.const 21#64] rfl
    (payload_read source "f0" pointer0 header0 payload0 flag0 cell0) installed guardRun
  obtain ⟨result,balanceBound,rootWidth,hashWidth,window,root,hash⟩ := nonce_setup_normal source post out pointer1 header1 payload1 flag1 pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash
    outputCell cell1 cell2 cell3 rootGlobal hashGlobal output domain installed returned setupRun
  exact ⟨result,stringFlags,nonceBound,balanceBound,rootWidth,hashWidth,window,root,hash⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_normal
