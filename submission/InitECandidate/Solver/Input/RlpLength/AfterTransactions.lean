import InitECandidate.Solver.Input.RlpLength.AfterTransactionsProgram

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The fixed transaction-list header, total/ommers additions, withdrawal
initialization and complete final phase. The preceding header-size premise
remains explicit; the transaction contribution is the checked aggregate bound. -/
theorem after_transactions_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer payload oldI : BitVec 64) (start count total txSum : Nat)
    (countSmall : count<2^31) (totalSmall : total≤2^31) (txBound : txSum≤817878932)
    (heap : Blob.HeapInput source input pointer) (inside : start+44*count≤input.length%2^64)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word oldI)))
    (t : source.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 txSum))))
    (mappedCount : source.memaddrs (payload+56#64)) (storedCount : source.memory (payload+56#64)=.word (BitVec.ofNat 64 count))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 start))
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 43*count+33≤source.clock) :
    ∃ target encoded paid,25*count≤encoded ∧ encoded≤total+txSum+57*count+28 ∧ paid≤43*count+33 ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source transactionSuffix=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "tl"]=some [.val (.word (BitVec.ofNat 64 txSum))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tl]
  obtain ⟨h,headerPaid,hLow,hHigh,headerBound,headerRun⟩:=ListHeader.call_execute source (BitVec.ofNat 64 txSum) "hl" [localVar "tl"] afterTransactionHeader args listCode headerCode beCode (by omega)
  let sh:=bind {source with clock:=source.clock-1-headerPaid} "hl" (BitVec.ofNat 64 h)
  have totalH : sh.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))) :=
    (bind_lookup_other _ "hl" "total" _ (by decide)).trans t
  have tlH : sh.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 txSum))) :=
    (bind_lookup_other _ "hl" "tl" _ (by decide)).trans tl
  have hlH : sh.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 h))):=bind_lookup_same _ _ _
  let combined:=total+h+txSum
  have addRead : eval sh addTransactionsExpression=some (.val (.word (BitVec.ofNat 64 combined))) := by
    simp [eval,addTransactionsExpression,evalHOLExact,evalListHOLExact,toExact,localVar,totalH,tlH,hlH,valueIsWord,valueWord,wordOpHOL,wordOp,
      combined,←BitVec.ofNat_add,Nat.add_assoc]
  let st:=bind sh "total" (BitVec.ofNat 64 combined)
  have addRun:=WitnessRadix.StateSteps.assign_execute sh "total" addTransactionsExpression _ _ totalH addRead
  have totalT : st.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 combined))):=bind_lookup_same _ _ _
  have ommersRead : eval st addOmmersExpression=some (.val (.word (BitVec.ofNat 64 (combined+1)))) := by
    simp [eval,addOmmersExpression,evalHOLExact,evalListHOLExact,toExact,localVar,totalT,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  let so:=bind st "total" (BitVec.ofNat 64 (combined+1))
  have ommersRun:=WitnessRadix.StateSteps.assign_execute st "total" addOmmersExpression _ _ totalT ommersRead
  have plO : so.locals.lookup (ofString "pl")=some (.val (.word payload)) :=
    (bind_lookup_other _ "total" "pl" _ (by decide)).trans ((bind_lookup_other _ "total" "pl" _ (by decide)).trans
      ((bind_lookup_other _ "hl" "pl" _ (by decide)).trans pl))
  have countMappedO : so.memaddrs (payload+56#64):=mappedCount
  have countStoredO : so.memory (payload+56#64)=.word (BitVec.ofNat 64 count):=storedCount
  have countRead : eval so withdrawalCountExpression=some (.val (.word (BitVec.ofNat 64 count))) := by
    simp [eval,withdrawalCountExpression,evalHOLExact,evalListHOLExact,toExact,localVar,plO,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,countMappedO,countStoredO]
  let sn:=bind so "nwd" (BitVec.ofNat 64 count)
  let sw:=bind sn "wl" 0#64
  let si:=bind sw "i" 0#64
  have iW : sw.locals.lookup (ofString "i")=some (.val (.word oldI)) :=
    (bind_lookup_other _ "wl" "i" _ (by decide)).trans ((bind_lookup_other _ "nwd" "i" _ (by decide)).trans
      ((bind_lookup_other _ "total" "i" _ (by decide)).trans ((bind_lookup_other _ "total" "i" _ (by decide)).trans
        ((bind_lookup_other _ "hl" "i" _ (by decide)).trans i))))
  have zeroRead : eval sw (.const 0#64)=some (.val (.word 0#64)):=rfl
  have resetRun:=WitnessRadix.StateSteps.assign_execute sw "i" (.const 0#64) oldI 0#64 iW zeroRead
  have plI : si.locals.lookup (ofString "pl")=some (.val (.word payload)) :=
    (bind_lookup_other _ "i" "pl" _ (by decide)).trans ((bind_lookup_other _ "wl" "pl" _ (by decide)).trans
      ((bind_lookup_other _ "nwd" "pl" _ (by decide)).trans plO))
  have iI : si.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have nI : si.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))) :=
    (bind_lookup_other _ "i" "nwd" _ (by decide)).trans ((bind_lookup_other _ "wl" "nwd" _ (by decide)).trans (bind_lookup_same _ _ _))
  have wlI : si.locals.lookup (ofString "wl")=some (.val (.word 0#64)) :=
    (bind_lookup_other _ "i" "wl" _ (by decide)).trans (bind_lookup_same _ _ _)
  have totalI : si.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 (combined+1)))) :=
    (bind_lookup_other _ "i" "total" _ (by decide)).trans ((bind_lookup_other _ "wl" "total" _ (by decide)).trans
      ((bind_lookup_other _ "nwd" "total" _ (by decide)).trans (bind_lookup_same _ _ _)))
  have hlI : si.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 h))) :=
    (bind_lookup_other _ "i" "hl" _ (by decide)).trans ((bind_lookup_other _ "wl" "hl" _ (by decide)).trans
      ((bind_lookup_other _ "nwd" "hl" _ (by decide)).trans ((bind_lookup_other _ "total" "hl" _ (by decide)).trans
        ((bind_lookup_other _ "total" "hl" _ (by decide)).trans hlH))))
  have heapI : Blob.HeapInput si input pointer:=Blob.HeapInput.of_fields source si input pointer rfl rfl rfl heap
  obtain ⟨target,encoded,phasePaid,lower,upper,phaseBound,number,phaseRun,phaseFrame⟩:=withdrawal_phase_execute si input pointer payload (BitVec.ofNat 64 h) start count (combined+1)
    countSmall (by dsimp [combined]; omega) heapI inside plI iI nI wlI totalI hlI mapped stored code wordCode listCode headerCode beCode
      (by change 43*count+22≤source.clock-1-headerPaid; omega)
  have resetAndPhase : evaluateHOLFiniteState sw (.seq (.assign .local (ofString "i") (.const 0#64)) withdrawalPhase)=
      (some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) := by
    rw [WitnessRadix.StateSteps.next_sequence sw si _ _ resetRun (Nat.le_refl _)]
    exact phaseRun
  have wlDeclared:=ScalarScope.declare_execute sn _ "wl" (.const 0#64) 0#64 _ _ rfl resetAndPhase
  have nDeclared:=ScalarScope.declare_execute so _ "nwd" withdrawalCountExpression (BitVec.ofNat 64 count) _ _ countRead wlDeclared
  have afterRun : evaluateHOLFiniteState sh afterTransactionHeader=
      (some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),restore so "nwd" (restore sn "wl" target)) := by
    rw [afterTransactionHeader,WitnessRadix.StateSteps.next_sequence sh st _ _ addRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence st so _ _ ommersRun (Nat.le_refl _)]
    exact nDeclared
  let final:=restore source "hl" (restore so "nwd" (restore sn "wl" target))
  let paid:=headerPaid+phasePaid+1
  refine ⟨final,encoded,paid,lower,by dsimp [combined] at upper; omega,by dsimp [paid]; omega,number,?_,?_⟩
  · rw [transaction_suffix_shape,headerRun,afterRun]
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid}
    rw [phaseFrame]
    have subtract : source.clock-1-headerPaid-phasePaid=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-headerPaid-phasePaid}=emptyLocalsHOLFinite {source with clock:=source.clock-paid}
    rw [subtract]

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.after_transactions_execute
