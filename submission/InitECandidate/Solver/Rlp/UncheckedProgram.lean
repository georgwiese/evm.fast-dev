import InitECandidate.Solver.Rlp.HeaderControl

namespace InitECandidate.Solver.Rlp.Unchecked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_item_total_unchecked with | .function fn=>progToHOL fn.body | _=>.skip
def afterByte : ProgHOL 64 := match body with | .dec _ _ _ rest=>rest | _=>.skip
def single : ProgHOL 64 := match afterByte with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterSingle : ProgHOL 64 := match afterByte with | .seq _ rest=>rest | _=>.skip
def shortString : ProgHOL 64 := match afterSingle with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterShortString : ProgHOL 64 := match afterSingle with | .seq _ rest=>rest | _=>.skip
def longString : ProgHOL 64 := match afterShortString with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterLongString : ProgHOL 64 := match afterShortString with | .seq _ rest=>rest | _=>.skip
def shortList : ProgHOL 64 := match afterLongString with | .seq (.ite _ yes _) _=>yes | _=>.skip
def longList : ProgHOL 64 := match afterLongString with | .seq _ rest=>rest | _=>.skip
def longCase (base : BitVec 64) (llName nName : String) : ProgHOL 64 :=
  .dec (ofString llName) .one (.op .sub [localVar "b",.const base])
    (.decCall (ofString nName) .one (ofString "rlp_read_length") [.op .add [localVar "p",.const 1#64],localVar llName]
      (.return (.op .add [.const 1#64,localVar llName,localVar nName])))

set_option maxRecDepth 10000
theorem body_shape : body=.dec (ofString "b") .one (.loadByte (localVar "p")) afterByte := by
  simp only [body,afterByte,localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem cases_shape : afterByte=
    .seq (.ite (.cmp .lower (localVar "b") (.const 128#64)) single .skip)
      (.seq (.ite (.cmp .notLower (.const 183#64) (localVar "b")) shortString .skip)
        (.seq (.ite (.cmp .notLower (.const 191#64) (localVar "b")) longString .skip)
          (.seq (.ite (.cmp .notLower (.const 247#64) (localVar "b")) shortList .skip) longList))) := by
  simp only [afterByte,body,single,afterSingle,shortString,afterShortString,longString,afterLongString,shortList,longList,
    localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem single_shape : single=.return (.const 1#64) := by
  simp only [single,afterByte,body,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem short_string_shape : shortString=.return (.op .sub [.op .add [.const 1#64,localVar "b"],.const 128#64]) := by
  simp only [shortString,afterSingle,afterByte,body,localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem short_list_shape : shortList=.return (.op .sub [.op .add [.const 1#64,localVar "b"],.const 192#64]) := by
  simp only [shortList,afterLongString,afterShortString,afterSingle,afterByte,body,localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem long_string_shape : longString=longCase 183#64 "ll" "n" := by
  simp only [longString,afterShortString,afterSingle,afterByte,body,longCase,localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem long_list_shape : longList=longCase 247#64 "ll2" "n2" := by
  simp only [longList,afterLongString,afterShortString,afterSingle,afterByte,body,longCase,localVar,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_item_total_unchecked")=some ([(ofString "p",.one)],body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 102 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_item_total_unchecked) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_rlp_item_total_unchecked,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Unchecked

#print axioms InitECandidate.Solver.Rlp.Unchecked.body_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.cases_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.single_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.short_string_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.short_list_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.long_string_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.long_list_shape
#print axioms InitECandidate.Solver.Rlp.Unchecked.original_code
