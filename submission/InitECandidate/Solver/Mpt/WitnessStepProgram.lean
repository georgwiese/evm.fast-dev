import InitECandidate.Solver.Rlp.DecodeProgram
import InitECandidate.Solver.Rlp.ItemSyntax

namespace InitECandidate.Solver.Mpt.WitnessStep
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | resolve | decode
  deriving DecidableEq

def original : Kind→Decl (BitVec 64)
  | .resolve=>Guest.Software.guestFn__resolve_step | .decode=>Guest.Software.guestFn__decode_step
def name : Kind→String | .resolve=>"_resolve_step" | .decode=>"_decode_step"
def index : Kind→Nat | .resolve=>234 | .decode=>235
def resultShape : Kind→ShapeHOL | .resolve=>Rlp.Item.resultShape | .decode=>.comb [.one,.one]
def body (kind : Kind) : ProgHOL 64 := match original kind with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "db",.one),(ofString "p",.one),(ofString "n",.one)]
def rlpName : Kind→String | .resolve=>"rlp_item" | .decode=>"rlp_decode_fully"
def rlpBody : Kind→ProgHOL 64 | .resolve=>Rlp.Item.body | .decode=>Rlp.Decode.body
def arguments : List (ExpHOL 64) := [localVar "p",localVar "n"]
def handler : ProgHOL 64 := .call (some (none,none)) (ofString "mpt_fail") [.const 3#64]
def caught (kind : Kind) : ProgHOL 64 :=
  .call (some (some (.local,ofString "it"),some (ofString "RlpErr",ofString "e",handler))) (ofString (rlpName kind)) arguments
def afterRlp (kind : Kind) : ProgHOL 64 := match body kind with
  | .dec _ _ _ (.dec _ _ _ (.seq _ rest))=>rest | _=>.skip
def parsed (kind : Kind) (pointer length : BitVec 64) (answer : ValueHOL 64) : Prop := match kind with
  | .resolve=>Rlp.Item.Valid pointer length.toNat answer | .decode=>Rlp.Decode.Complete pointer length answer

set_option maxRecDepth 100000 in
theorem body_shape (kind : Kind) : body kind=
    .dec (ofString "it") Rlp.Item.resultShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
      (.dec (ofString "e") .one (.const 0#64) (.seq (caught kind) (afterRlp kind))) := by
  cases kind <;> simp only [body,original,afterRlp,caught,rlpName,arguments,handler,Rlp.Item.resultShape,localVar,
    Guest.Software.guestFn__resolve_step,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString (name kind))=some (formals,body kind,resultShape kind) := by
  have checked:=Input.OriginalCode.indexed code installed (index kind) (GasBudget.OriginalCodeEnvironment.originalEntry (original kind)) (by cases kind <;> rfl)
  cases kind <;> simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,original,name,resultShape,Rlp.Item.resultShape,
    Guest.Software.guestFn__resolve_step,Guest.Software.guestFn__decode_step,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem rlp_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString (rlpName kind))=some (Rlp.Header.formals,rlpBody kind,Rlp.Item.resultShape) := by
  cases kind with
  | resolve=>exact Rlp.Item.original_code code installed
  | decode=>exact Rlp.Decode.original_code code installed

theorem parsed_valid (kind : Kind) (pointer length : BitVec 64) (answer : ValueHOL 64)
    (actual : parsed kind pointer length answer) : Rlp.Item.Valid pointer length.toNat answer := by
  cases kind with
  | resolve=>exact actual
  | decode=>
    obtain ⟨header,payload,flag,value,small,positive,extent,binary,listHeader⟩:=actual
    exact ⟨header,payload,flag,value,small,positive,Nat.le_of_eq extent,binary,listHeader⟩

end InitECandidate.Solver.Mpt.WitnessStep

#print axioms InitECandidate.Solver.Mpt.WitnessStep.body_shape
#print axioms InitECandidate.Solver.Mpt.WitnessStep.original_code
#print axioms InitECandidate.Solver.Mpt.WitnessStep.rlp_code
#print axioms InitECandidate.Solver.Mpt.WitnessStep.parsed_valid
