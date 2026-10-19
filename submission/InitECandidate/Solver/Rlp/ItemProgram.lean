import InitECandidate.Solver.Rlp.ListCountCall

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_item with | .function fn=>progToHOL fn.body | _=>.skip
def resultShape : ShapeHOL := .comb [.one,.one,.one,.one]
def afterGuard : ProgHOL 64 := match body with | .seq _ rest=>rest | _=>.skip
def afterByte : ProgHOL 64 := match afterGuard with | .dec _ _ _ rest=>rest | _=>.skip
def single : ProgHOL 64 := match afterByte with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterSingle : ProgHOL 64 := match afterByte with | .seq _ rest=>rest | _=>.skip
def shortString : ProgHOL 64 := match afterSingle with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterShortString : ProgHOL 64 := match afterSingle with | .seq _ rest=>rest | _=>.skip
def longString : ProgHOL 64 := match afterShortString with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterLongString : ProgHOL 64 := match afterShortString with | .seq _ rest=>rest | _=>.skip
def shortList : ProgHOL 64 := match afterLongString with | .seq (.ite _ yes _) _=>yes | _=>.skip
def longList : ProgHOL 64 := match afterLongString with | .seq _ rest=>rest | _=>.skip
def shortReturn (flag : BitVec 64) : ProgHOL 64 := .return (.rstruct [.const flag,.op .add [localVar "p",.const 1#64],localVar "n",.op .add [.const 1#64,localVar "n"]])
def longReturn (flag : BitVec 64) : ProgHOL 64 := .return (.rstruct [.const flag,.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n",.op .add [.const 1#64,localVar "ll",localVar "n"]])
def shortCount : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_list_count") [.op .add [localVar "p",.const 1#64],localVar "n"]
def longCount : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_list_count") [.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n"]
def longTail (flag : BitVec 64) : ProgHOL 64 := if flag=0#64 then longReturn flag else .seq longCount (longReturn flag)
def afterRead (flag : BitVec 64) : ProgHOL 64 :=
  .seq (.ite (.cmp .notLower (.const 55#64) (localVar "n")) (Header.fail 5#64) .skip)
    (.seq (.ite (.cmp .lower (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"]) (localVar "n")) (Header.fail 3#64) .skip) (longTail flag))
def longCase (base flag : BitVec 64) : ProgHOL 64 := .dec (ofString "ll") .one (.op .sub [localVar "b",.const base])
  (.seq Header.lengthGuard (.decCall (ofString "n") .one (ofString "rlp_read_length") Header.readArguments (afterRead flag)))

set_option maxRecDepth 10000
theorem body_shape : body=.seq (.ite (.cmp .equal (localVar "len") (.const 0#64)) (Header.fail 1#64) .skip) afterGuard := by
  simp only [body,afterGuard,Header.fail,localVar,Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem byte_shape : afterGuard=.dec (ofString "b") .one (.loadByte (localVar "p")) afterByte := by
  simp only [afterGuard,afterByte,body,Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem cases_shape : afterByte=
    .seq (.ite (.cmp .lower (localVar "b") (.const 128#64)) single .skip)
      (.seq (.ite (.cmp .notLower (.const 183#64) (localVar "b")) shortString .skip)
        (.seq (.ite (.cmp .notLower (.const 191#64) (localVar "b")) longString .skip)
          (.seq (.ite (.cmp .notLower (.const 247#64) (localVar "b")) shortList .skip) longList))) := by
  simp only [afterByte,afterGuard,body,single,afterSingle,shortString,afterShortString,longString,afterLongString,shortList,longList,
    Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem single_shape : single=.return (.rstruct [.const 0#64,localVar "p",.const 1#64,.const 1#64]) := by
  simp only [single,afterByte,afterGuard,body,localVar,Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem short_string_shape : shortString=.dec (ofString "n") .one (.op .sub [localVar "b",.const 128#64])
    (.seq Header.shortGuard (.seq Header.canonicalGuard (shortReturn 0#64))) := by
  simp only [shortString,afterSingle,afterByte,afterGuard,body,Header.shortGuard,Header.canonicalGuard,shortReturn,Header.fail,localVar,
    Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem short_list_shape : shortList=.dec (ofString "n") .one (.op .sub [localVar "b",.const 192#64])
    (.seq Header.shortGuard (.seq shortCount (shortReturn 1#64))) := by
  simp only [shortList,afterLongString,afterShortString,afterSingle,afterByte,afterGuard,body,Header.shortGuard,shortCount,shortReturn,Header.fail,localVar,
    Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem long_string_shape : longString=longCase 183#64 0#64 := by
  simp only [longString,afterShortString,afterSingle,afterByte,afterGuard,body,longCase,Header.lengthGuard,Header.readArguments,afterRead,longTail,if_pos rfl,ite_true,longReturn,Header.fail,localVar,
    Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem long_list_shape : longList=longCase 247#64 1#64 := by
  simp only [longList,afterLongString,afterShortString,afterSingle,afterByte,afterGuard,body,longCase,Header.lengthGuard,Header.readArguments,afterRead,longTail,
    if_neg (show (1#64 : BitVec 64)≠0#64 from by decide),longCount,longReturn,Header.fail,localVar,
    Guest.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_item")=some (Header.formals,body,resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 95 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_item) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,resultShape,
    Guest.guestFn_rlp_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.body_shape
#print axioms InitECandidate.Solver.Rlp.Item.byte_shape
#print axioms InitECandidate.Solver.Rlp.Item.cases_shape
#print axioms InitECandidate.Solver.Rlp.Item.single_shape
#print axioms InitECandidate.Solver.Rlp.Item.short_string_shape
#print axioms InitECandidate.Solver.Rlp.Item.short_list_shape
#print axioms InitECandidate.Solver.Rlp.Item.long_string_shape
#print axioms InitECandidate.Solver.Rlp.Item.long_list_shape
#print axioms InitECandidate.Solver.Rlp.Item.original_code
