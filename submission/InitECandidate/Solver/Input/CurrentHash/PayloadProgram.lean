import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.PanTraversal
import Guest.Model

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htr_payload with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "pl",.one),(ofString "out",.one)]
def transactionLoop : ProgHOL 64 := (BuildProgram.loops body)[0]?.getD .skip
def withdrawalLoop : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def transactionStep : ProgHOL 64 := match transactionLoop with | .while _ step=>step | _=>.skip
def withdrawalStep : ProgHOL 64 := match withdrawalLoop with | .while _ step=>step | _=>.skip
def transactionTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "ntx")
def withdrawalTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "nwd")
def transactionArguments : List (ExpHOL 64) := [
  .load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64]]),
  .load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64]),
  .op .add [localVar "roots",.panop .mul [localVar "i",.const 32#64]]]
def withdrawalArguments : List (ExpHOL 64) := [
  .op .add [localVar "wd",.panop .mul [localVar "i",.const 44#64]],
  .op .add [localVar "roots",.panop .mul [localVar "i",.const 32#64]]]
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])

set_option maxRecDepth 100000 in
theorem loop_shapes : transactionLoop=.while transactionTest transactionStep ∧
    transactionStep=.seq (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments) increment ∧
    withdrawalLoop=.while withdrawalTest withdrawalStep ∧
    withdrawalStep=.seq (.call (some (none,none)) (ofString "htr_withdrawal") withdrawalArguments) increment := by
  simp only [transactionLoop,transactionStep,withdrawalLoop,withdrawalStep,BuildProgram.loops,body,Guest.Software.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,
    transactionTest,withdrawalTest,transactionArguments,withdrawalArguments,increment,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_payload")=some (formals,body,.one) := by
  simpa only [Code.name,Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_htr_payload,shapeToHOL,paramToHOL,List.map_cons,List.map_nil]
    using Code.installed code installed .htr_payload

theorem transaction_step_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key transactionStep := by
  rw [loop_shapes.2.1]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem withdrawal_step_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key withdrawalStep := by
  rw [loop_shapes.2.2.2]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.loop_shapes
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.original_code
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.transaction_step_local
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.withdrawal_step_local
