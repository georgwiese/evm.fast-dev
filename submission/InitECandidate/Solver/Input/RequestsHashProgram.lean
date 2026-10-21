import InitECandidate.Solver.Input.RequestListHashMemory
import InitECandidate.Solver.Input.PContainerMemory
import InitECandidate.Solver.Input.PContainerGlobals

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev Kind := RequestListHash.Kind

def body : ProgHOL 64 := match Guest.guestFn_htr_requests with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "rq",.one),(ofString "out",.one)]
def outputExpression (kind : Kind) : ExpHOL 64 := if kind.tag=0 then localVar "ch" else .op .add [localVar "ch",.const (BitVec.ofNat 64 (32*kind.tag))]
def arguments (kind : Kind) : List (ExpHOL 64) := [.const (BitVec.ofNat 64 kind.tag),
  .load .one (.op .add [localVar "rq",.const (BitVec.ofNat 64 (16*kind.tag))]),
  .load .one (.op .add [localVar "rq",.const (BitVec.ofNat 64 (16*kind.tag+8))]),
  .const (BitVec.ofNat 64 kind.record.length),outputExpression kind]
def step (kind : Kind) : ProgHOL 64 := .call (some (none,none)) (ofString "htr_request_list") (arguments kind)
def containerArguments : List (ExpHOL 64) := [localVar "ch",.const 5#64,localVar "out"]
def afterLists : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_pcontainer") containerArguments) FixedHash.releaseSuffix
def pipeline (kinds : List Kind) : ProgHOL 64 := kinds.foldr (fun kind rest=>.seq (step kind) rest) afterLists
def afterAllocation : ProgHOL 64 := pipeline RequestListHash.kinds
def allocationArguments : List (ExpHOL 64) := [.panop .mul [.const 5#64,.const 32#64]]
def afterMark : ProgHOL 64 := .decCall (ofString "ch") .one (ofString "alloc") allocationArguments afterAllocation

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,Guest.guestFn_htr_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterMark,afterAllocation,pipeline,RequestListHash.kinds,List.foldr_cons,List.foldr_nil,afterLists,FixedHash.releaseSuffix,step,arguments,outputExpression,
    RequestListHash.Kind.tag,RequestListHash.Kind.record,FixedHash.Kind.length,containerArguments,allocationArguments,localVar]
  rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_requests")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 202 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_requests) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_requests,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem tag_bound (kind : Kind) : kind.tag<5 := by cases kind <;> decide

theorem step_globals (kind : Kind) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code (step kind) :=
  GlobalEffects.call_body key code (some none) (ofString "htr_request_list") (arguments kind) RequestListHash.formals RequestListHash.body .one
    (RequestListHash.original_code code installed) (RequestListHash.globals key code installed different)

theorem after_lists_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code afterLists :=
  GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "htr_pcontainer") containerArguments PContainer.formals PContainer.body .one
      (PContainer.original_code code installed) (PContainer.globals key code installed different))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) (Merkle.release_globals key code different)) (GlobalEffects.returned key code _))

theorem pipeline_globals (kinds : List Kind) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code (pipeline kinds) := by
  induction kinds with
  | nil=>exact after_lists_globals key code installed different
  | cons kind rest ih=>exact GlobalEffects.sequence key code _ _ (step_globals kind key code installed different) ih

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.body_shape
#print axioms InitECandidate.Solver.Input.RequestsHash.original_code
#print axioms InitECandidate.Solver.Input.RequestsHash.tag_bound
#print axioms InitECandidate.Solver.Input.RequestsHash.step_globals
#print axioms InitECandidate.Solver.Input.RequestsHash.after_lists_globals
#print axioms InitECandidate.Solver.Input.RequestsHash.pipeline_globals
