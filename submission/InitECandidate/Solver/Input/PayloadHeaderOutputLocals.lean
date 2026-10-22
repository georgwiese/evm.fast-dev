import InitECandidate.Solver.Input.PayloadHeaderCompleted

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure OutputBindings (current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  transactions : current.locals.lookup (ofString "txr")=some (.val (.word (afterOmmerHeap heap)))
  withdrawals : current.locals.lookup (ofString "wr")=some (.val (.word (withdrawalBase heap)))
  requests : current.locals.lookup (ofString "rh")=some (.val (.word (requestsBase heap)))
  balance : current.locals.lookup (ofString "bh")=some (.val (.word (balanceBase heap)))

theorem complete_output_bindings (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) :
    OutputBindings (completeHeader input source hashed heap words) heap := by
  constructor <;>
    simp [completeHeader,balancePointerStored,allocatedBalance,requestsPointerStored,allocatedRequests,
      beforeRequests,withdrawalScalarsStored,payloadFieldsStored,withdrawalScalarFields,withdrawalPointerStored,allocatedWithdrawal,
      baseFeeStored,wideStored,feeEntry,zeroPointerStored,clearedZero,allocatedZero,beforeZero,scalarPrefixStored,scalarFields,
      wideZeroStored,bloomPointerStored,receiptsPointerStored,transactionPointerStored,allocatedTransactionRoot,
      storedField,allocatedField,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem OutputBindings.after_length (current target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (bindings : OutputBindings current heap) (value : ValueHOL 64) :
    OutputBindings (CallNormal.continuationEntry current target "bl" value) heap := by
  constructor
  · simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using bindings.transactions
  · simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using bindings.withdrawals
  · simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using bindings.requests
  · simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using bindings.balance

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.complete_output_bindings
#print axioms InitECandidate.Solver.Input.PayloadHeader.OutputBindings.after_length
