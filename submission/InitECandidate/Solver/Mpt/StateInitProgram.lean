import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_state_init with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "nodedb",.one),(ofString "state_root",.one),(ofString "codedb",.one)]
def allocate : ProgHOL 64 := .call (some (some (.global,ofString "ws"),none)) (ofString "alloc") [.const 40#64]
def store (offset : Nat) (name : String) : ProgHOL 64 :=
  .store (.op .add [.var .global (ofString "ws"),.const (BitVec.ofNat 64 offset)]) (localVar name)
def afterAllocation : ProgHOL 64 := match body with | .seq _ rest=>rest | _=>.skip
def afterFirst : ProgHOL 64 := match afterAllocation with | .seq _ rest=>rest | _=>.skip
def afterSecond : ProgHOL 64 := match afterFirst with | .seq _ rest=>rest | _=>.skip
def rootCall : ProgHOL 64 := match afterSecond with | .seq _ rest=>rest | _=>.skip
def afterRoot : ProgHOL 64 := match rootCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def rootArguments : List (ExpHOL 64) := [localVar "nodedb",localVar "state_root"]

set_option maxRecDepth 100000

/-- Literal original322 through its real workspace allocation and stores,
up to the unchanged root materializer call. -/
theorem shapes : body=.seq allocate afterAllocation ∧
    afterAllocation=.seq (store 0 "nodedb") afterFirst ∧ afterFirst=.seq (store 8 "state_root") afterSecond ∧
    afterSecond=.seq (store 16 "codedb") rootCall ∧
    rootCall=.decCall (ofString "root") .one (ofString "decode_witness_to_mpt") rootArguments afterRoot := by
  simp only [body,Guest.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    allocate,store,afterAllocation,afterFirst,afterSecond,rootCall,afterRoot,rootArguments,localVar]
  trivial

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "state_init")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 322 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_state_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_state_init,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.shapes
#print axioms InitECandidate.Solver.Mpt.StateInit.original_code
