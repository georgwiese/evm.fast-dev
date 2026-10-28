import InitECandidate.Solver.Input.CurrentHash.PayloadProgram

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def dropSequence : Nat→ProgHOL 64→ProgHOL 64 | 0,program=>program | n+1,.seq _ tail=>dropSequence n tail | _,_=>.skip
def afterRaw : ProgHOL 64 := match body with | .dec _ _ _ tail=>tail | _=>.skip
def afterMark : ProgHOL 64 := match afterRaw with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterChunks : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail=>tail | _=>.skip
def transactionScope : ProgHOL 64 := dropSequence 13 afterChunks
def afterTxs : ProgHOL 64 := match transactionScope with | .dec _ _ _ tail=>tail | _=>.skip
def afterNtx : ProgHOL 64 := match afterTxs with | .dec _ _ _ tail=>tail | _=>.skip
def afterSecondMark : ProgHOL 64 := match afterNtx with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterTxRoots : ProgHOL 64 := match afterSecondMark with | .decCall _ _ _ _ tail=>tail | _=>.skip
def transactionLoopAndSuffix : ProgHOL 64 := match afterTxRoots with | .dec _ _ _ tail=>tail | _=>.skip
def afterTransactionLoop : ProgHOL 64 := match transactionLoopAndSuffix with | .seq _ tail=>tail | _=>.skip
def afterTransactionList : ProgHOL 64 := match afterTransactionLoop with | .seq _ tail=>tail | _=>.skip
def withdrawalScope : ProgHOL 64 := match afterTransactionList with | .seq _ tail=>tail | _=>.skip
def afterWd : ProgHOL 64 := match withdrawalScope with | .dec _ _ _ tail=>tail | _=>.skip
def afterNwd : ProgHOL 64 := match afterWd with | .dec _ _ _ tail=>tail | _=>.skip
def afterWithdrawalAllocation : ProgHOL 64 := match afterNwd with | .seq _ tail=>tail | _=>.skip
def withdrawalLoopAndSuffix : ProgHOL 64 := match afterWithdrawalAllocation with | .seq _ tail=>tail | _=>.skip
def afterWithdrawalLoop : ProgHOL 64 := match withdrawalLoopAndSuffix with | .seq _ tail=>tail | _=>.skip
def afterWithdrawalList : ProgHOL 64 := match afterWithdrawalLoop with | .seq _ tail=>tail | _=>.skip
def finalFields : ProgHOL 64 := match afterWithdrawalList with | .seq _ tail=>tail | _=>.skip

def fieldExpression (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const (BitVec.ofNat 64 offset)])
def rootsAllocationArguments (count : String) : List (ExpHOL 64) := [.op .add [.panop .mul [localVar count,.const 32#64],.const 32#64]]
def listArguments (count : String) (slot : Nat) : List (ExpHOL 64) := [localVar "roots",localVar count,localVar count,
  .op .add [localVar "ch",.const (BitVec.ofNat 64 (32*slot))]]

set_option maxRecDepth 100000 in
theorem entry_shapes : body=.dec (ofString "raw") .one (fieldExpression 0) afterRaw ∧
    afterRaw=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 19#64,.const 32#64]] afterChunks := by
  simp only [afterRaw,afterMark,afterChunks,body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,fieldExpression,localVar]
  exact ⟨True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem transaction_shapes :
    transactionScope=.dec (ofString "txs") .one (fieldExpression 32) afterTxs ∧
    afterTxs=.dec (ofString "ntx") .one (fieldExpression 40) afterNtx ∧
    afterNtx=.decCall (ofString "m2") .one (ofString "heap_mark") [] afterSecondMark ∧
    afterSecondMark=.decCall (ofString "roots") .one (ofString "alloc") (rootsAllocationArguments "ntx") afterTxRoots ∧
    afterTxRoots=.dec (ofString "i") .one (.const 0#64) transactionLoopAndSuffix ∧
    transactionLoopAndSuffix=.seq transactionLoop afterTransactionLoop ∧
    afterTransactionLoop=.seq (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments "ntx" 13)) afterTransactionList ∧
    afterTransactionList=.seq (.call (some (none,none)) (ofString "heap_release") [localVar "m2"]) withdrawalScope := by
  simp only [transactionScope,dropSequence,afterChunks,afterMark,afterRaw,afterTxs,afterNtx,afterSecondMark,afterTxRoots,
    transactionLoopAndSuffix,afterTransactionLoop,afterTransactionList,withdrawalScope,transactionLoop,BuildProgram.loops,body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,Option.map_some,
    fieldExpression,rootsAllocationArguments,listArguments,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem withdrawal_shapes :
    withdrawalScope=.dec (ofString "wd") .one (fieldExpression 48) afterWd ∧
    afterWd=.dec (ofString "nwd") .one (fieldExpression 56) afterNwd ∧
    afterNwd=.seq (.call (some (some (.local,ofString "roots"),none)) (ofString "alloc") (rootsAllocationArguments "nwd")) afterWithdrawalAllocation ∧
    afterWithdrawalAllocation=.seq (.assign .local (ofString "i") (.const 0#64)) withdrawalLoopAndSuffix ∧
    withdrawalLoopAndSuffix=.seq withdrawalLoop afterWithdrawalLoop ∧
    afterWithdrawalLoop=.seq (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments "nwd" 14)) afterWithdrawalList ∧
    afterWithdrawalList=.seq (.call (some (none,none)) (ofString "heap_release") [localVar "m2"]) finalFields := by
  simp only [transactionScope,dropSequence,afterChunks,afterMark,afterRaw,afterTxs,afterNtx,afterSecondMark,afterTxRoots,
    transactionLoopAndSuffix,afterTransactionLoop,afterTransactionList,withdrawalScope,afterWd,afterNwd,afterWithdrawalAllocation,
    withdrawalLoopAndSuffix,afterWithdrawalLoop,afterWithdrawalList,finalFields,withdrawalLoop,BuildProgram.loops,body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,Option.map_some,
    fieldExpression,rootsAllocationArguments,listArguments,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.entry_shapes
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.transaction_shapes
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.withdrawal_shapes
