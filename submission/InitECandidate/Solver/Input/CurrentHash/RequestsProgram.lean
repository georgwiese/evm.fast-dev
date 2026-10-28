import InitECandidate.Solver.Input.CurrentHash.RequestListProgram
import InitECandidate.Solver.Input.SavedHeapReturn

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := Code.body .htr_requests
def field (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "rq",.const (BitVec.ofNat 64 offset)])
def outputExpression (index : Nat) : ExpHOL 64 := if index=0 then localVar "ch" else .op .add [localVar "ch",.const (BitVec.ofNat 64 (32*index))]
def arguments (kind : RequestList.Kind) : List (ExpHOL 64) := [.const (BitVec.ofNat 64 kind.tag),field (16*kind.tag),field (16*kind.tag+8),
  .const (BitVec.ofNat 64 kind.record.length),outputExpression kind.tag]
def listCall (kind : RequestList.Kind) : ProgHOL 64 := .call (some (none,none)) (Code.name .htr_request_list) (arguments kind)
def pipeline (kinds : List RequestList.Kind) (tail : ProgHOL 64) := kinds.foldr (fun kind rest=>.seq (listCall kind) rest) tail

def afterLists : ProgHOL 64 := .seq (.call (some (none,none)) (Code.name .htr_pcontainer) [localVar "ch",.const 5#64,localVar "out"]) FixedRecord.releaseSuffix
def afterAllocation : ProgHOL 64 := pipeline RequestList.kinds afterLists
def afterMark : ProgHOL 64 := .decCall (ofString "ch") .one (Code.name .alloc) [.panop .mul [.const 5#64,.const 32#64]] afterAllocation

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark := by
  simp only [body,afterMark,afterAllocation,pipeline,RequestList.kinds,List.foldr_cons,List.foldr_nil,listCall,arguments,field,outputExpression,afterLists,
    FixedRecord.releaseSuffix,RequestList.Kind.tag,RequestList.Kind.record,FixedRecord.Kind.length,Code.name,
    Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_htr_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  rfl

theorem pipeline_local (key : MlS) (kinds : List RequestList.Kind) : LocalPrefix key (pipeline kinds .skip) := by
  induction kinds with
  | nil=>exact .skip
  | cons kind rest ih=>exact .seq (.call none _ _ (by intro name impossible; cases impossible)) ih

theorem pipeline_tail (kinds : List RequestList.Kind) (rest : ProgHOL 64) (tail : SavedHeapReturn.Tail "mark" rest) : SavedHeapReturn.Tail "mark" (pipeline kinds rest) := by
  induction kinds with
  | nil=>exact tail
  | cons kind rest ih=>exact SavedHeapReturn.Tail.ignored_call _ _ ih

theorem saved_tail : SavedHeapReturn.Tail "mark" afterMark :=
  .decCall "ch" .one _ _ (by decide) (pipeline_tail _ afterLists (SavedHeapReturn.Tail.ignored_call _ _ .release))

/-- Actual parent request hashing restores its entering heap independently of
counts, data/workspace mapping and all intermediate allocator-room conditions. -/
theorem body_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [body_shape] at actual
  exact SavedHeapReturn.marked_scope source post "mark" cursor afterMark saved_tail installed heap value actual

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.body_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.pipeline_local
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.pipeline_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.saved_tail
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.body_heap
