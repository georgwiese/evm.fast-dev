import InitECandidate.Solver.Input.MainSecpBlock
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Main.SecpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_secp256k1_init with | .function fn => progToHOL fn.body | _ => .skip
def action : InitializerAllocations.Action := ⟨"secp_accel_scratch",448,.op .add [.panop .mul [.const 2#64,.const 160#64],.const 128#64]⟩
def actions : List InitializerAllocations.Action := [action]
def prime : SecpBlock.Words := fun index => if index.val = 0 then 18446744069414583343#64 else 18446744073709551615#64
def order : SecpBlock.Words := fun index => match index.val with
  | 0 => 13822214165235122497#64
  | 1 => 13451932020343611451#64
  | 2 => 18446744073709551614#64
  | _ => 18446744073709551615#64

def quadExpression (words : SecpBlock.Words) : ExpHOL 64 :=
  .rstruct [.const (words 0),.const (words 1),.const (words 2),.const (words 3)]
def blockCall (offset : Nat) (words : SecpBlock.Words) : ProgHOL 64 :=
  .call (some (none,none)) (ofString "secp_accel_init_block")
    [.op .add [.var .global (ofString "secp_accel_scratch"),.const (BitVec.ofNat 64 offset)],quadExpression words]
def afterAllocation : ProgHOL 64 := .seq (blockCall 0 prime) (.seq (blockCall 160 order) (.return (.const 0#64)))
def guard : ProgHOL 64 := .ite (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0#64)) (.return (.const 0#64)) .skip
def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  SecpBlock.template (SecpBlock.template (allocated source cursor) (BitVec.ofNat 64 cursor) prime) (BitVec.ofNat 64 (cursor + 160)) order

theorem body_shape : body = .seq guard (InitializerAllocations.withTail actions afterAllocation) := by
  simp only [body,guard,actions,action,afterAllocation,blockCall,quadExpression,prime,order,InitializerAllocations.withTail,InitializerAllocations.call,
    Guest.guestFn_secp256k1_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  rfl

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem scratch_member : ofString "secp_accel_scratch" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem valid : ∀ current,current ∈ actions → InitializerAllocations.Valid current := by
  intro current member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst current
  exact ⟨scratch_member,by decide,by decide,fun _ => rfl⟩

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "secp256k1_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 135 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_secp256k1_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_secp256k1_init,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem allocated_scratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "secp_accel_scratch") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp [allocated,InitializerAllocations.template,InitializerAllocations.reserve,actions,action,putGlobal,HolFiniteMapExact.update,FUPDATE]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template SecpBlock.template allocated
  rw [InitializerAllocations.template_clock]

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  simp only [template,SecpBlock.template,InitializerAllocations.context_memory]
  exact InitializerAllocations.template_context source cursor actions

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor).globals :=
  InitializerAllocations.template_scalars source cursor actions scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 448)))) :=
  InitializerAllocations.template_heap source cursor actions heap valid

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notScratch : key ≠ ofString "secp_accel_scratch") :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocations.template_other source cursor actions key notHeap
  intro current member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst current
  exact notScratch

end InitECandidate.Solver.Input.Main.SecpInitialization

#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.scratch_member
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.original_code
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.allocated_scratch
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.template_other
