import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Mpt.NewTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_mpt_new with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "root_node",.one),(ofString "secured",.one)]
def values (root secured : BitVec 64) : List (ValueHOL 64):=[.val (.word root),.val (.word secured)]
def address (offset : Nat) : ExpHOL 64:=.op .add [localVar "m",.const (BitVec.ofNat 64 offset)]
def storeRoot : ProgHOL 64:=.store (address 0) (localVar "root_node")
def storeSecured : ProgHOL 64:=.store (address 8) (localVar "secured")
def tail : ProgHOL 64:=.seq storeRoot (.seq storeSecured (.return (localVar "m")))
def actions : List Input.CallPrefix.Action:=[.scoped (ofString "m") .one (ofString "alloc") [.const 16#64]]

theorem body_shape : body=.decCall (ofString "m") .one (ofString "alloc") [.const 16#64] tail := by
  simp only [body,Guest.guestFn_mpt_new,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,tail,storeRoot,storeSecured,address,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mpt_new")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 242 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_mpt_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_mpt_new,Guest.guestFn_mpt_new,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem body_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 2 := by
  rw [body_shape]
  apply PersistentAlloc.scoped_price code installed (ofString "m") .one _ _ 0
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.returned code _))

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (root secured : BitVec 64)
    (code : codeFn (ofString "mpt_new")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "mpt_new") (values root secured)=some (body,callee,.one) ∧
      callee.lookup (ofString "root_node")=some (.val (.word root)) ∧ callee.lookup (ofString "secured")=some (.val (.word secured)) :=
  Input.word_pair_environment codeFn (ofString "mpt_new") (ofString "root_node") (ofString "secured") body .one root secured (by decide) code

theorem allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current inner,Input.CallPrefix.Execution source actions current ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current tail=(some (.returned value),inner) := by
  rw [body_shape] at normal
  exact Input.CallPrefix.normal_trace source post actions tail value (Input.NoReturn.scoped_call _ _ _ _ _ Input.NoReturn.skip) normal

end InitECandidate.Solver.Mpt.NewTrie

#print axioms InitECandidate.Solver.Mpt.NewTrie.body_shape
#print axioms InitECandidate.Solver.Mpt.NewTrie.original_code
#print axioms InitECandidate.Solver.Mpt.NewTrie.body_cost
#print axioms InitECandidate.Solver.Mpt.NewTrie.environment
#print axioms InitECandidate.Solver.Mpt.NewTrie.allocation_trace
