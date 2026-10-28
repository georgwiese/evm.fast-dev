import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.CurrentTable.NewStores
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_new_node with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t",.one)]
def afterFree : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def freeBranch : ProgHOL 64 := match afterFree with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterFreeGuard : ProgHOL 64 := match afterFree with | .seq _ rest => rest | _ => .skip
def afterNext : ProgHOL 64 := match afterFreeGuard with | .dec _ _ _ rest => rest | _ => .skip
def growBranch : ProgHOL 64 := match afterNext with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterGrow : ProgHOL 64 := match afterNext with | .seq _ rest => rest | _ => .skip
def afterNode : ProgHOL 64 := match afterGrow with | .dec _ _ _ rest => rest | _ => .skip

def address (offset : Nat) : ExpHOL 64 := Scalar.plus (localVar "t") offset
def freeGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "f") (.const 0#64)) freeBranch .skip
def growGuard : ProgHOL 64 := .ite (.cmp .lower (.load .one (address 80)) (localVar "next")) growBranch .skip

set_option maxRecDepth 100000 in
theorem shapes :
    body = .dec (ofString "f") .one (.load .one (address 72)) afterFree ∧
    afterFree = .seq freeGuard afterFreeGuard ∧
    afterFreeGuard = .dec (ofString "next") .one (.load .one (address 64)) afterNext ∧
    afterNext = .seq growGuard afterGrow ∧
    afterGrow = .dec (ofString "n") .one (.load .one (address 64)) afterNode ∧
    afterNode = .seq (.store (address 64) (.op .add [localVar "n",.const 1#64])) (.return (localVar "n")) := by
  simp only [body,afterFree,freeBranch,afterFreeGuard,afterNext,growBranch,afterGrow,afterNode,
    address,freeGuard,growGuard,Guest.Software.guestFn_htab_new_node,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Scalar.plus,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_new_node") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 122
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_new_node) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_new_node,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- A real mapped field of the current88-byte Patricia header. -/
theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table value : BitVec 64) (offset : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : WitnessRadix.AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8 = 0) (inside : offset < 88) (offsetAligned : offset%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (cell : source.memory (table+BitVec.ofNat 64 offset) = .word value) :
    eval source (.load .one (address offset)) = some (.val (.word value)) := by
  exact Witness.load_word_read source (address offset) (table+BitVec.ofNat 64 offset) value
    (Scalar.plus_read source (localVar "t") table offset (Request.local_word source "t" table tableCell))
    (WitnessRadix.AllocatedBytes.word_mapped source table 88 offset domain arena inside aligned offsetAligned) cell

end InitECandidate.Solver.Input.CurrentTable.NewNode

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.original_code
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.field_read
