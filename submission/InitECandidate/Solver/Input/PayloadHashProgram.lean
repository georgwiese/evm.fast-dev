import InitECandidate.Solver.Input.PBytesMemory
import InitECandidate.Solver.Input.FixedHashMemory
import InitECandidate.Solver.Input.BytesListMemory
import InitECandidate.Solver.Input.PContainerMemory
import InitECandidate.Solver.PanTraversal

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_payload with | .function fn=>progToHOL fn.body | _=>.skip
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
  simp only [transactionLoop,transactionStep,withdrawalLoop,withdrawalStep,BuildProgram.loops,body,Guest.guestFn_htr_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,
    transactionTest,withdrawalTest,transactionArguments,withdrawalArguments,increment,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_payload")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 195 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_payload) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_payload,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem transaction_step_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key transactionStep := by
  rw [loop_shapes.2.1]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem withdrawal_step_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key withdrawalStep := by
  rw [loop_shapes.2.2.2]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem transaction_step_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code transactionStep := by
  rw [loop_shapes.2.1]
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "htr_pbytes") transactionArguments PBytes.formals PBytes.body .one
      (PBytes.original_code code installed) (PBytes.globals key code installed different)) (GlobalEffects.assign key code _ _)

theorem withdrawal_step_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code withdrawalStep := by
  rw [loop_shapes.2.2.2]
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "htr_withdrawal") withdrawalArguments FixedHash.Kind.withdrawal.formals FixedHash.Kind.withdrawal.body .one
      (FixedHash.original_code .withdrawal code installed) (FixedHash.globals .withdrawal key code installed different)) (GlobalEffects.assign key code _ _)

end InitECandidate.Solver.Input.PayloadHash

#print axioms InitECandidate.Solver.Input.PayloadHash.loop_shapes
#print axioms InitECandidate.Solver.Input.PayloadHash.original_code
#print axioms InitECandidate.Solver.Input.PayloadHash.transaction_step_local
#print axioms InitECandidate.Solver.Input.PayloadHash.withdrawal_step_local
#print axioms InitECandidate.Solver.Input.PayloadHash.transaction_step_globals
#print axioms InitECandidate.Solver.Input.PayloadHash.withdrawal_step_globals
