import InitECandidate.Solver.Input.RunAttemptTransactionTrace
import InitECandidate.Solver.Input.MainStateInitCallerLocals

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual decoded payload supplies both original precheck loads at
their genuine lexical scopes. Its count is charged to the input byte budget. -/
theorem transaction_reads (input : Guest.InputBlob) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (frame : HashInput.Frame origin source inputPointer.toNat root.toNat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (bindings : CallerLocals input source) :
    eval source RunAttempt.transactionArrayExpression=some (.val (.word (PayloadHashData.description input).transactions)) ∧
    eval (QueryBranch.bind source "txs" (PayloadHashData.description input).transactions) RunAttempt.transactionCountExpression=
      some (.val (.word (BitVec.ofNat 64 (Payload.transactionCount input)))) ∧
    Payload.transactionCount input≤(input.length%2^64)/4 ∧ Payload.transactionCount input<2^63 := by
  let data:=PayloadHashData.description input
  have image : data.Image origin:=prepared.image.payload
  have layout : data.Layout inputPointer.toNat root.toNat (input.length%2^64):=prepared.layout.payload
  have arrayRead:=data.field_read origin source _ _ _ image layout frame domain bindings.payload
    (32,data.transactions) (by simp [PayloadHash.Description.cells])
  let next:=QueryBranch.bind source "txs" data.transactions
  have nextFrame:=frame.of_memory origin source next _ _ rfl
  have payload : next.locals.lookup (ofString "pl")=some (.val (.word data.payload)):=
    (bind_lookup_other source "txs" "pl" data.transactions (by decide)).trans bindings.payload
  have countRead:=data.field_read origin next _ _ _ image layout nextFrame domain payload
    (40,BitVec.ofNat 64 data.transactionCount) (by simp [PayloadHash.Description.cells])
  have bounded : Payload.transactionCount input≤(input.length%2^64)/4:=layout.transactionCountBound
  refine ⟨arrayRead,countRead,bounded,?_⟩
  have small:=layout.budgetBound
  omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.transaction_reads
