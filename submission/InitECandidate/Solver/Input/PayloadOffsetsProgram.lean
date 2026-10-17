import InitECandidate.Solver.Input.PayloadPrefixSetup

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def storeExtra : ProgHOL 64 := .store Header.offsets (localVar "o_extra")
def storeTransactions : ProgHOL 64 := .store (Scalar.plus Header.offsets 8) (localVar "o_txs")
def storeWithdrawals : ProgHOL 64 := .store (Scalar.plus Header.offsets 16) (localVar "o_wd")
def storeBalances : ProgHOL 64 := .store (Scalar.plus Header.offsets 24) (localVar "o_bal")
def guardArguments : List (ExpHOL 64) := [Header.offsets,.const 4#64,.const 540#64,localVar "len"]
def guardCall : ProgHOL 64 := .call (some (none,none)) (ofString "ssz_check_offsets") guardArguments
def offsetContinuation : ProgHOL 64 := dropLeading 5 offsetBody

theorem offset_body_shape : offsetBody=.seq storeExtra (.seq storeTransactions (.seq storeWithdrawals (.seq storeBalances (.seq guardCall offsetContinuation)))) := by
  simp only [offsetBody,dropLeading,afterGuard,body,Scalar.payloadBody,Guest.guestFn_decode_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,offsetContinuation,storeExtra,storeTransactions,storeWithdrawals,storeBalances,guardCall,guardArguments,
    Header.offsets,Scalar.plus,localVar]

def extraStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {source with memory:=WitnessRadix.StoreWord.put source.memory array (offsetWords input 0)}
def transactionsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {extraStored source input array with memory:=WitnessRadix.StoreWord.put (extraStored source input array).memory (array+8#64) (offsetWords input 1)}
def withdrawalsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {transactionsStored source input array with memory:=WitnessRadix.StoreWord.put (transactionsStored source input array).memory (array+16#64) (offsetWords input 2)}
def offsetsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {withdrawalsStored source input array with memory:=WitnessRadix.StoreWord.put (withdrawalsStored source input array).memory (array+24#64) (offsetWords input 3)}

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.offset_body_shape
