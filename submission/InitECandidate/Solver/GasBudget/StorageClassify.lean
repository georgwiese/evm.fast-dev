import InitECandidate.Solver.GasBudget.StorageTests

namespace InitECandidate.Solver.GasBudget.StorageTests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

def zeroWords : U256Eq.Quad:=fun _=>0#64

theorem zero_word (a : U256Eq.Quad) : U256Zero.resultWord a=boolWord (decide (a=zeroWords)) := by
  classical
  have equivalence : U256Zero.mixed a=0#64 ↔ a=zeroWords := by
    rw [U256Zero.mixed_zero]
    exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩
  by_cases same : a=zeroWords
  · have mixed:=(equivalence.mpr same)
    rw [U256Zero.resultWord,if_pos mixed]
    simp [boolWord,same]
  · have mixed : U256Zero.mixed a≠0#64:=fun h=>same (equivalence.mp h)
    simp [U256Zero.resultWord,boolWord,same,mixed]

theorem equality_word (a b : U256Eq.Quad) : U256Eq.resultWord a b=boolWord (decide (a=b)) := by
  classical
  by_cases same : a=b <;> simp [U256Eq.resultWord,boolWord,same]

/-- The actual guards, when fed the proved equality/zero outputs, implement
exactly the two storage state-fee predicates used in StorageDebt.transition. -/
theorem actual_guards (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original current next : U256Eq.Quad)
    (oc : source.locals.lookup (ofString "oc")=some (.val (.word (U256Eq.resultWord original current))))
    (cn : source.locals.lookup (ofString "cn")=some (.val (.word (U256Eq.resultWord current next))))
    (onValue : source.locals.lookup (ofString "on")=some (.val (.word (U256Eq.resultWord original next))))
    (oz : source.locals.lookup (ofString "oz")=some (.val (.word (U256Zero.resultWord original)))) :
    eval source chargeTest=some (.val (.word (boolWord (decide (original=current ∧ current≠next ∧ original=zeroWords))))) ∧
    eval source refundTest=some (.val (.word (boolWord (decide (current≠next ∧ original=next ∧ original=zeroWords))))) := by
  classical
  rw [equality_word] at oc cn onValue
  rw [zero_word] at oz
  have charge:=charge_read source (decide (original=current)) (decide (current=next)) (decide (original=zeroWords)) oc cn oz
  have refund:=refund_read source (decide (current=next)) (decide (original=next)) (decide (original=zeroWords)) cn onValue oz
  constructor
  · simpa only [Bool.decide_and,decide_not,Bool.and_assoc] using charge
  · simpa only [Bool.decide_and,decide_not,Bool.and_assoc] using refund

/-- Observing these actual0/1 guards yields a balanced per-slot ledger entry.
This is conditional on real backend values, not a whole-opcode trace claim. -/
theorem observed_debt (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original current next : U256Eq.Quad)
    (oc : source.locals.lookup (ofString "oc")=some (.val (.word (U256Eq.resultWord original current))))
    (cn : source.locals.lookup (ofString "cn")=some (.val (.word (U256Eq.resultWord current next))))
    (onValue : source.locals.lookup (ofString "on")=some (.val (.word (U256Eq.resultWord original next))))
    (oz : source.locals.lookup (ofString "oz")=some (.val (.word (U256Zero.resultWord original)))) :
    (if eval source chargeTest=some (.val (.word 1#64)) then 97920 else 0)+StorageDebt.debt zeroWords original current 97920=
      (if eval source refundTest=some (.val (.word 1#64)) then 97920 else 0)+StorageDebt.debt zeroWords original next 97920 := by
  classical
  have guards:=actual_guards source original current next oc cn onValue oz
  rw [guards.1,guards.2]
  have charged : (if some (.val (.word (boolWord (decide (original=current ∧ current≠next ∧ original=zeroWords)))))=
      (some (.val (.word 1#64)) : Option (ValueHOL 64)) then 97920 else 0)=StorageDebt.charged zeroWords original current next 97920 := by
    by_cases active : original=current ∧ current≠next ∧ original=zeroWords <;> simp [boolWord,StorageDebt.charged,active]
  have refunded : (if some (.val (.word (boolWord (decide (current≠next ∧ original=next ∧ original=zeroWords)))))=
      (some (.val (.word 1#64)) : Option (ValueHOL 64)) then 97920 else 0)=StorageDebt.refunded zeroWords original current next 97920 := by
    by_cases active : current≠next ∧ original=next ∧ original=zeroWords <;> simp [boolWord,StorageDebt.refunded,active]
  rw [charged,refunded]
  exact StorageDebt.transition zeroWords original current next 97920

end InitECandidate.Solver.GasBudget.StorageTests

#print axioms InitECandidate.Solver.GasBudget.StorageTests.zero_word
#print axioms InitECandidate.Solver.GasBudget.StorageTests.equality_word
#print axioms InitECandidate.Solver.GasBudget.StorageTests.actual_guards
#print axioms InitECandidate.Solver.GasBudget.StorageTests.observed_debt
