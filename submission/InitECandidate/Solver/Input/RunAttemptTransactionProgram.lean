import InitECandidate.Solver.Input.RunAttemptStateInitProgram
import InitECandidate.Solver.Input.SignedGuardedCounterLoop

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionArrayExpression : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const 32#64])
def transactionCountExpression : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const 40#64])
def transactionTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "ntx")
def transactionLengthExpression : ExpHOL 64 := .load .one (.op .add
  [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64])
def emptyTransactionGuard : ProgHOL 64 := .ite (.cmp .equal transactionLengthExpression (.const 0#64))
  (.raise (ofString "BlockErr") (.const 4#64)) .skip
def transactionIncrement : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def transactionStep : ProgHOL 64 := .seq emptyTransactionGuard transactionIncrement
def transactionScan : ProgHOL 64 := .while transactionTest transactionStep
def transactionDeclarations : ProgHOL 64 := match afterStateInit with | .seq _ rest=>rest | _=>.skip
def afterTransactionArray : ProgHOL 64 := match transactionDeclarations with | .dec _ _ _ rest=>rest | _=>.skip
def afterTransactionCount : ProgHOL 64 := match afterTransactionArray with | .dec _ _ _ rest=>rest | _=>.skip
def transactionScanTail : ProgHOL 64 := match afterTransactionCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterTransactionScan : ProgHOL 64 := match transactionScanTail with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- Literal unchanged original815 after state_init, including its signed
comparison, sixteen-byte slice records and real BlockErr4 guard. -/
theorem transaction_shapes :
    afterStateInit=.seq .skip transactionDeclarations ∧
    transactionDeclarations=.dec (ofString "txs") .one transactionArrayExpression afterTransactionArray ∧
    afterTransactionArray=.dec (ofString "ntx") .one transactionCountExpression afterTransactionCount ∧
    afterTransactionCount=.dec (ofString "i") .one (.const 0#64) transactionScanTail ∧
    transactionScanTail=.seq transactionScan afterTransactionScan := by
  simp only [afterStateInit,afterCodes,afterNodes,constructors,afterParent,afterCount,afterHeaders,headerCall,afterPayload,body,
    Guest.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    transactionDeclarations,afterTransactionArray,afterTransactionCount,transactionScanTail,afterTransactionScan,
    transactionScan,transactionTest,transactionStep,emptyTransactionGuard,transactionLengthExpression,transactionIncrement,
    transactionArrayExpression,transactionCountExpression,localVar]
  trivial

theorem transaction_guarded : GuardedCounter 1 transactionStep :=
  .checks (.ite _ (.raised _ _) .skip) .increment

/-- The real precheck has one source tick per record at most, on every
outcome, including unreadable slices, empty transactions and timeouts. -/
theorem transaction_scan_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^63)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source transactionScan).2.clock≤length := by
  have priced:=SignedGuardedCounterLoop.cost (ofString "ntx") transactionStep length (by decide) small transaction_guarded source
    ⟨0#64,counter,count,by simp⟩
  simpa only [transactionScan,transactionTest,localVar,SignedGuardedCounterLoop.rank,CounterFlow.counterWord,
    counter,Option.getD_some,valueWord,BitVec.toNat_ofNat,Nat.zero_mod,Nat.sub_zero] using priced

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.transaction_shapes
#print axioms InitECandidate.Solver.Input.RunAttempt.transaction_guarded
#print axioms InitECandidate.Solver.Input.RunAttempt.transaction_scan_cost
