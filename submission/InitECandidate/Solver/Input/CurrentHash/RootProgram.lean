import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.SavedHeapReturn
import Guest.Model

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Step where | payload | headers | header | requests

def body : ProgHOL 64 := Code.body .htr_new_payload_request
def formals : List (MlS×ShapeHOL) := [(ofString "si",.one),(ofString "out",.one)]
def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ rest=>rest | _=>.skip
def field (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "si",.const (BitVec.ofNat 64 offset)])
def outputExpression (offset : Nat) : ExpHOL 64 := .op .add [localVar "ch",.const (BitVec.ofNat 64 offset)]
def Step.routine : Step→Code.Routine | .payload=>.htr_payload | .headers=>.htr_plist_chunks | .header=>.memcpy | .requests=>.htr_requests
def Step.arguments : Step→List (ExpHOL 64)
  | .payload=>[field 0,localVar "ch"]
  | .headers=>[field 8,field 16,field 16,outputExpression 32]
  | .header=>[outputExpression 64,field 24,.const 32#64]
  | .requests=>[field 32,outputExpression 96]
def Step.call (step : Step) : ProgHOL 64 := .call (some (none,none)) (Code.name step.routine) step.arguments
def steps : List Step := [.payload,.headers,.header,.requests]
def pipeline (items : List Step) (tail : ProgHOL 64) : ProgHOL 64 := items.foldr (fun step rest=>.seq step.call rest) tail
def merkleArguments : List (ExpHOL 64) := [localVar "ch",.const 4#64,.const 4#64,localVar "out"]
def releaseSuffix : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))
def afterLists : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "merkleize") merkleArguments) releaseSuffix

set_option maxRecDepth 100000 in
theorem source_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 4#64,.const 32#64]] afterAllocation ∧
    afterAllocation=pipeline steps afterLists := by
  simp only [body,afterMark,afterAllocation,Code.body,Code.entry,Code.declaration,Code.name,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_new_payload_request,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    pipeline,steps,List.foldr_cons,List.foldr_nil,Step.call,Step.arguments,Step.routine,field,outputExpression,afterLists,merkleArguments,releaseSuffix,localVar]
  exact ⟨True.intro,True.intro,True.intro⟩

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_new_payload_request")=some (formals,body,.one) := by
  simpa only [Code.name,Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_htr_new_payload_request,shapeToHOL,paramToHOL,List.map_cons,List.map_nil]
    using Code.installed code installed .htr_new_payload_request

theorem pipeline_local (items : List Step) (key : MlS) : LocalPrefix key (pipeline items .skip) := by
  induction items with
  | nil=>exact .skip
  | cons item rest ih=>exact .seq (.call none _ _ (by intro name impossible; cases impossible)) ih

theorem after_lists_tail : SavedHeapReturn.Tail "mark" afterLists := .ignored_call _ _ .release

theorem pipeline_tail (items : List Step) : SavedHeapReturn.Tail "mark" (pipeline items afterLists) := by
  induction items with
  | nil=>exact after_lists_tail
  | cons item rest ih=>exact .ignored_call _ _ ih

theorem body_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [source_shape.1] at actual
  apply SavedHeapReturn.marked_scope source post "mark" cursor afterMark _ installed heap value actual
  rw [source_shape.2.1,source_shape.2.2]
  exact .decCall "ch" .one _ _ (by decide) (pipeline_tail steps)

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.original_code
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.pipeline_local
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.body_heap
