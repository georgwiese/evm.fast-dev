import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.CurrentHash.PackBytesCost

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Kind where | withdrawal | deposit | wdreq | cons | bdep | bexit
  deriving DecidableEq

def Kind.routine : Kind → Code.Routine
  | .withdrawal => .htr_withdrawal | .deposit => .htr_deposit | .wdreq => .htr_wdreq
  | .cons => .htr_cons | .bdep => .htr_bdep | .bexit => .htr_bexit
def Kind.declaration (kind : Kind) := Code.declaration kind.routine
def Kind.name (kind : Kind) := Code.name kind.routine
def Kind.inputName : Kind→String | .withdrawal=>"w" | _=>"e"
def Kind.length : Kind→Nat | .withdrawal=>44 | .deposit=>192 | .wdreq=>76 | .cons=>116 | .bdep=>184 | .bexit=>68
def Kind.count : Kind→Nat | .withdrawal=>4 | .deposit=>5 | .wdreq=>3 | .cons=>3 | .bdep=>4 | .bexit=>2
def Kind.depth : Kind→Nat | .withdrawal=>2 | .deposit=>3 | .wdreq=>2 | .cons=>2 | .bdep=>2 | .bexit=>1
def Kind.body (kind : Kind) : ProgHOL 64 := Code.body kind.routine
def Kind.formals (kind : Kind) : List (MlS×ShapeHOL) := [(ofString kind.inputName,.one),(ofString "out",.one)]

inductive Step where
  | scalar (offset field : Nat)
  | copy (offset field : Nat)
  | vector (offset length field depth : Nat)
  deriving DecidableEq

def offsetExpression (name : String) (offset : Nat) : ExpHOL 64 := if offset=0 then localVar name else .op .add [localVar name,.const (BitVec.ofNat 64 offset)]
def Step.inputOffset : Step→Nat | .scalar offset _ | .copy offset _ | .vector offset _ _ _=>offset
def Step.field : Step→Nat | .scalar _ field | .copy _ field | .vector _ _ field _=>field
def Step.length : Step→Nat | .scalar _ _=>8 | .copy _ _=>32 | .vector _ length _ _=>length
def Step.function : Step→MlS | .scalar _ _=>ofString "htr_u64_at" | .copy _ _=>ofString "memcpy" | .vector _ _ _ _=>ofString "htr_bytes_vector"
def Step.arguments (step : Step) (inputName : String) : List (ExpHOL 64) :=
  let p:=offsetExpression inputName step.inputOffset
  let out:=offsetExpression "ch" (32*step.field)
  match step with | .scalar _ _=>[p,out] | .copy _ _=>[out,p,.const 32#64] | .vector _ length _ _=>[p,.const (BitVec.ofNat 64 length),out]
def Step.program (step : Step) (inputName : String) : ProgHOL 64 := .call (some (none,none)) step.function (step.arguments inputName)
def Step.price : Step→Nat
  | .scalar _ _ => 54
  | .copy _ _ => 42
  | .vector _ length _ depth => PackBytesCost.price length + 88*PackBytes.chunks length + 4*depth + 53

def Kind.steps : Kind→List Step
  | .withdrawal=>[.scalar 0 0,.scalar 8 1,.vector 16 20 2 0,.scalar 36 3]
  | .deposit=>[.vector 0 48 0 1,.copy 48 1,.scalar 80 2,.vector 88 96 3 2,.scalar 184 4]
  | .wdreq=>[.vector 0 20 0 0,.vector 20 48 1 1,.scalar 68 2]
  | .cons=>[.vector 0 20 0 0,.vector 20 48 1 1,.vector 68 48 2 1]
  | .bdep=>[.vector 0 48 0 1,.copy 48 1,.scalar 80 2,.vector 88 96 3 2]
  | .bexit=>[.vector 0 20 0 0,.vector 20 48 1 1]

def releaseSuffix : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))
def Kind.merkleArguments (kind : Kind) : List (ExpHOL 64) := [localVar "ch",.const (BitVec.ofNat 64 kind.count),.const (BitVec.ofNat 64 kind.count),localVar "out"]
def Kind.afterSteps (kind : Kind) : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "merkleize") kind.merkleArguments) releaseSuffix
def pipeline (inputName : String) (steps : List Step) (tail : ProgHOL 64) := steps.foldr (fun step rest=>.seq (step.program inputName) rest) tail
def Kind.afterAllocation (kind : Kind) : ProgHOL 64 := pipeline kind.inputName kind.steps kind.afterSteps
def Kind.allocationArguments (kind : Kind) : List (ExpHOL 64) := [.panop .mul [.const (BitVec.ofNat 64 kind.count),.const 32#64]]
def Kind.afterMark (kind : Kind) : ProgHOL 64 := .decCall (ofString "ch") .one (ofString "alloc") kind.allocationArguments kind.afterAllocation

set_option maxRecDepth 100000 in
theorem body_shape (kind : Kind) : kind.body=.decCall (ofString "mark") .one (ofString "heap_mark") [] kind.afterMark := by
  cases kind <;> simp only [Kind.body,Kind.routine,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_withdrawal,Guest.Software.guestFn_htr_deposit,Guest.Software.guestFn_htr_wdreq,
    Guest.Software.guestFn_htr_cons,Guest.Software.guestFn_htr_bdep,Guest.Software.guestFn_htr_bexit,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    Kind.afterMark,Kind.afterAllocation,Kind.allocationArguments,Kind.afterSteps,Kind.merkleArguments,Kind.inputName,Kind.count,Kind.steps,
    pipeline,List.foldr_cons,List.foldr_nil,Step.program,Step.function,Step.arguments,Step.field,Step.inputOffset,offsetExpression,releaseSuffix,localVar] <;> rfl

set_option maxRecDepth 100000 in
theorem original_code (kind : Kind) (code) (installed : OriginalCode.Installed code) : code.lookup kind.name=some (kind.formals,kind.body,.one) := by
  have checked := Code.installed code installed kind.routine
  cases kind <;> simpa only [Kind.routine,Kind.formals,Kind.body,Kind.name,Kind.inputName,
    Code.name,Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_htr_withdrawal,Guest.Software.guestFn_htr_deposit,Guest.Software.guestFn_htr_wdreq,
    Guest.Software.guestFn_htr_cons,Guest.Software.guestFn_htr_bdep,Guest.Software.guestFn_htr_bexit,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.body_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.original_code
