import InitECandidate.Solver.Mpt.AccountAfterDecodeCost
import InitECandidate.Solver.Mpt.AccountDecodeCaught
import InitECandidate.Solver.Input.ClockCostCurrentValue

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Complete unchanged decode_account_from_leaf269, on every source
outcome. Its actual caught decode, list conversion, count guard, four field
calls, nonce/balance loops and output suffix are included. Heap/input/output
and scratch geometry are current entry facts, still requiring reachability. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤191*length.toNat+292 := by
  let zeroItem : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
  let tupled := setVarHOLFinite (ofString "it") zeroItem source
  let entered := bind tupled "e" 0#64
  have tupleOther (name : String) (other : ofString "it"≠ofString name) : tupled.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    simp [tupled,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other]
  have currentPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "e" "p" _ (by decide)).trans ((tupleOther "p" (by decide)).trans pointerCell)
  have currentLength : entered.locals.lookup (ofString "n")=some (.val (.word length)) :=
    (bind_lookup_other _ "e" "n" _ (by decide)).trans ((tupleOther "n" (by decide)).trans lengthCell)
  have currentOutput : entered.locals.lookup (ofString "acct_out")=some (.val (.word out)) :=
    (bind_lookup_other _ "e" "acct_out" _ (by decide)).trans ((tupleOther "acct_out" (by decide)).trans outputCell)
  have currentArena := Rlp.Validation.Arena.of_fields source entered cursor limit arena rfl rfl
  have fits : pointer.toNat+length.toNat<2^64 := by have := heap.isLt; omega
  have firstCost := caught_cost entered pointer length cursor limit currentPointer currentLength currentArena fits installed
  have joined := Input.ClockCost.sequence_reached_current entered caught afterDecode (60*length.toNat+45) (131*length.toNat+247) firstCost ?_
  · rw [body_shape]
    have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem := by
      simp [zeroItem,eval,evalHOLExact,evalListHOLExact]
    apply Input.ClockCost.declared_value_current source (ofString "it") Rlp.Item.resultShape _ zeroItem _ (191*length.toNat+292) zeroRead
    apply Input.ClockCost.declared_current tupled "e" (.const 0#64) 0#64 _ (191*length.toNat+292) rfl
    change entered.clock-(evaluateHOLFiniteState entered (.seq caught afterDecode)).2.clock≤191*length.toNat+292
    omega
  · intro middle normal
    obtain ⟨positive,post,answer,complete,nextArena,above,domain,endian,codeEq,heapEq,price,middleEq⟩ :=
      caught_none entered middle pointer length cursor limit currentPointer currentLength currentArena fits installed normal
    have middleArena := Rlp.Validation.Arena.of_fields post middle cursor limit nextArena (by rw [middleEq]; rfl) (by rw [middleEq]; rfl)
    have middleItem : middle.locals.lookup (ofString "it")=some answer := by
      rw [middleEq]
      exact Input.CallNormal.continuation_lookup_same entered post "it" answer
    have middleOutput : middle.locals.lookup (ofString "acct_out")=some (.val (.word out)) := by
      rw [middleEq]
      exact (Input.CallNormal.continuation_lookup_other entered post "it" "acct_out" answer (by decide)).trans currentOutput
    have middleHeap : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
      rw [middleEq]
      exact heapEq.trans heapGlobal
    have middleInstalled : Input.OriginalCode.Installed middle.code := by
      rw [middleEq]
      change Input.OriginalCode.Installed post.code
      rw [codeEq]
      exact installed
    exact after_decode_cost middle pointer length heap cursor limit out cutoff answer middleItem complete middleOutput middleArena
      middleHeap heapBound before sizeBound aligned scratchBelow inputAbove output middleInstalled

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_cost
