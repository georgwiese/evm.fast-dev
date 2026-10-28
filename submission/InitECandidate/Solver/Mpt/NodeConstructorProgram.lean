import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

inductive Kind where | hashed | leaf | extension | branch
  deriving DecidableEq

def original : Kind→Decl (BitVec 64)
  | .hashed=>Guest.Software.guestFn_node_new_hashed | .leaf=>Guest.Software.guestFn_node_new_leaf
  | .extension=>Guest.Software.guestFn_node_new_ext | .branch=>Guest.Software.guestFn_node_new_branch
def name : Kind→String
  | .hashed=>"node_new_hashed" | .leaf=>"node_new_leaf" | .extension=>"node_new_ext" | .branch=>"node_new_branch"
def index : Kind→Nat | .hashed=>229 | .leaf=>230 | .extension=>231 | .branch=>232
def bytes : Kind→Nat | .hashed=>32 | .leaf=>64 | .extension=>56 | .branch=>176
def formals : Kind→List (MlS×ShapeHOL)
  | .hashed=>[(ofString "hash",.one)]
  | .leaf=>[(ofString "nib",.one),(ofString "nlen",.one),(ofString "vptr",.one),(ofString "vlen",.one)]
  | .extension=>[(ofString "nib",.one),(ofString "nlen",.one),(ofString "child",.one)]
  | .branch=>[]
def body (kind : Kind) : ProgHOL 64 := match original kind with | .function fn=>progToHOL fn.body | _=>.skip
def tail (kind : Kind) : ProgHOL 64 := match body kind with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- All four actual original constructors start at their genuine fixed-size
persistent allocation. The original memory writes remain in their real tail. -/
theorem allocation_shape (kind : Kind) : body kind=.decCall (ofString "nd") .one (ofString "alloc") [.const (BitVec.ofNat 64 (bytes kind))] (tail kind) := by
  cases kind <;> simp only [body,tail,original,bytes,Guest.Software.guestFn_node_new_hashed,Guest.Software.guestFn_node_new_leaf,Guest.Software.guestFn_node_new_ext,Guest.Software.guestFn_node_new_branch,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString (name kind))=some (formals kind,body kind,.one) := by
  have checked:=Input.OriginalCode.indexed code installed (index kind) (GasBudget.OriginalCodeEnvironment.originalEntry (original kind)) (by cases kind <;> rfl)
  cases kind <;> simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,original,name,
    Guest.Software.guestFn_node_new_hashed,Guest.Software.guestFn_node_new_leaf,Guest.Software.guestFn_node_new_ext,Guest.Software.guestFn_node_new_branch,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.allocation_shape
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.original_code
