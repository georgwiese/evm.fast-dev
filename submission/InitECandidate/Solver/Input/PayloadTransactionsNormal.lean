import InitECandidate.Solver.Input.PayloadExtraStores

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem transaction_range (input : Guest.InputBlob) (length : BitVec 64)
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position)
    (inside : 62+length.toNat≤input.length%2^64) :
    540≤Guest.GasLimit.le32 input 566 ∧ Guest.GasLimit.le32 input 566≤Guest.GasLimit.le32 input 570 ∧
      62+Guest.GasLimit.le32 input 570≤input.length%2^64 := by
  have first:=valid 1 (by decide)
  have second:=valid 2 (by decide)
  change 540≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat ∧ _ at first
  change _ ∧ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat≤length.toNat ∧
    (0<2→(BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat) at second
  simp only [RawScalar.le32_number] at first second
  exact ⟨first.1,second.2.2 (by decide),by omega⟩

/-- Whole actual extra-data prefix and transaction-list caller on every normal
payload path. No schema validity is assumed for the transaction list itself. -/
theorem transactions_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor array length : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position)
    (inside : 62+length.toNat≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (code : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (enough : (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+3≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtra=(some (.returned value),post)) :
    ∃ next innerPost returned,
      returned=(if Guest.GasLimit.le32 input 570=Guest.GasLimit.le32 input 566 then VarList.emptyValue
        else VarList.pairValue array (Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4)) ∧
      next.locals=source.locals.update (ofString "txs",returned) ∧
      Blob.HeapInput next input pointer ∧
      (∀ query : BitVec 64,query.toNat<array.toNat→next.memory query=(extraStoredPayload source input pointer cursor).memory query) ∧
      source.clock-((Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+2)≤next.clock ∧ next.clock≤source.clock ∧
      WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
        (if Guest.GasLimit.le32 input 570=Guest.GasLimit.le32 input 566 then source
         else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4)))) ∧
      evaluateHOLFiniteState next afterTransactions=(some (.returned value),innerPost) ∧
      post=restore source "txs" innerPost ∧
      VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566) ≤
        (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4 := by
  classical
  obtain ⟨lower,ordered,contained⟩:=transaction_range input length valid inside
  obtain ⟨prefixRun,prefixHeap⟩:=extra_stores source input pointer cursor heap p pl e t lower domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom
  let stored:=extraStoredPayload source input pointer cursor
  have tailRun : evaluateHOLFiniteState stored transactionCall=(some (.returned value),post):=prefixRun.symm.trans run
  have args:=transaction_arguments stored input pointer p t w ordered contained
  rw [transactions_shape.2.1] at tailRun
  obtain ⟨next,innerPost,returned,valueEq,localsEq,clockEq,controlEq,nextHeap,oldMemory,clockLower,clockUpper,nextRun,postEq,records,countLimit⟩:=
    VarList.caller_normal stored post input pointer array 9223372036854775807#64
      (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)
      prefixHeap args.2 domain pointerLower pointerAligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape
      "txs" transactionArguments afterTransactions args.1 code enough value tailRun
  have emptyEq : (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566=0)↔
      Guest.GasLimit.le32 input 570=Guest.GasLimit.le32 input 566 := by omega
  refine ⟨next,innerPost,returned,?_,localsEq,nextHeap,oldMemory,clockLower,clockUpper,?_,nextRun,postEq,?_⟩
  · simpa only [emptyEq] using valueEq
  · by_cases empty : Guest.GasLimit.le32 input 570=Guest.GasLimit.le32 input 566
    · simp only [emptyEq,if_pos empty] at controlEq ⊢
      exact controlEq.trans ((field_control _ _ _ _).trans (field_control _ _ _ _))
    · simp only [emptyEq,if_neg empty] at controlEq ⊢
      exact controlEq.trans ((allocated_field_control _ _ _ _ _ _).trans (allocated_field_control _ _ _ _ _ _))

  · by_cases empty : Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566=0
    · simp [VarList.decodedCount,empty]
    · simp only [VarList.decodedCount,if_neg empty]
      simp only [if_neg empty] at clockEq
      change next.clock=source.clock-1-(Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4+1) at clockEq
      have low : source.clock-((Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+2)≤next.clock := clockLower
      omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.transaction_range
#print axioms InitECandidate.Solver.Input.Payload.transactions_normal
