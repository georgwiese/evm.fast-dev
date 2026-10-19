import InitECandidate.Solver.Mpt.AccountDecodeProgram
import InitECandidate.Solver.Rlp.ItemValue
import InitECandidate.Solver.Input.CounterExpressionCost
import InitECandidate.Solver.Input.CounterDeclaration

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem nonce_body_price (code) : Input.ClockCost.Bound code nonceLoopBody 0 := by
  rw [nonce_body_shape]
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)

theorem balance_body_price (code) : Input.ClockCost.Bound code balanceLoopBody 0 := by
  rw [balance_body_shape]
  apply Input.ClockCost.declared
  apply Input.ClockCost.declared
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.assign code _ _)

theorem nonce_body_safe : Input.LocalPrefix (ofString "f0") nonceLoopBody := by
  rw [nonce_body_shape]
  exact .seq (.assign _ _ (by decide)) (.assign _ _ (by decide))

theorem balance_body_safe : Input.LocalPrefix (ofString "f1") balanceLoopBody := by
  rw [balance_body_shape]
  exact .dec _ _ _ (by decide) (.dec _ _ _ (by decide) (.seq (.store _ _) (.assign _ _ (by decide))))

theorem nonce_body_advances : Input.CounterFlow.Advances (ofString "i") 1 nonceLoopBody := by
  rw [nonce_body_shape]
  apply Input.CounterFlow.sequence (ofString "i") nonceAccumulate increment 0 1
  · exact Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))
  · exact Input.CounterFlow.increment _

theorem balance_body_advances : Input.CounterFlow.Advances (ofString "i") 1 balanceLoopBody := by
  rw [balance_body_shape]
  apply Input.CounterFlow.declared _ _ _ _ _ 1 (by decide)
  apply Input.CounterFlow.declared _ _ _ _ _ 1 (by decide)
  apply Input.CounterFlow.sequence (ofString "i") balanceStore increment 0 1
  · exact Input.CounterFlow.preserved _ _ (.store _ _)
  · exact Input.CounterFlow.increment _

theorem payload_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (pointer header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (Rlp.Item.result pointer header payload flag)) :
    eval source (field name 2)=some (.val (.word payload)) := by
  simp [field,eval,evalHOLExact,localVar,toExact,cell,Rlp.Item.result]

theorem nonce_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag index : BitVec 64)
    (cell : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer header payload flag))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤payload.toNat) :
    source.clock-(evaluateHOLFiniteState source nonceLoop).2.clock≤payload.toNat-index.toNat := by
  rw [nonce_loop_shape]
  simpa only [Nat.zero_add,Nat.one_mul,localVar] using Input.CounterFlow.expression_loop_cost source.code (ofString "i") (ofString "f0")
    (Rlp.Item.result pointer header payload flag) (field "f0" 2) nonceLoopBody 0 payload.toNat payload.isLt
    (by intro current currentCell; simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using payload_read current "f0" pointer header payload flag currentCell)
    (nonce_body_price source.code) nonce_body_advances nonce_body_safe source index rfl indexCell cell bounded

theorem balance_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag index : BitVec 64)
    (cell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤payload.toNat) :
    source.clock-(evaluateHOLFiniteState source balanceLoop).2.clock≤payload.toNat-index.toNat := by
  rw [balance_loop_shape]
  simpa only [Nat.zero_add,Nat.one_mul,localVar] using Input.CounterFlow.expression_loop_cost source.code (ofString "i") (ofString "f1")
    (Rlp.Item.result pointer header payload flag) (field "f1" 2) balanceLoopBody 0 payload.toNat payload.isLt
    (by intro current currentCell; simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using payload_read current "f1" pointer header payload flag currentCell)
    (balance_body_price source.code) balance_body_advances balance_body_safe source index rfl indexCell cell bounded

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_body_price
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_price
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_body_safe
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_safe
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_body_advances
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_advances
#print axioms InitECandidate.Solver.Mpt.AccountDecode.payload_read
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_loop_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_loop_cost
