import InitECandidate.Solver.Rlp.ReadLengthCall
import InitECandidate.Solver.Rlp.FailGuard
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_item_header with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "len",.one)]
def resultShape : ShapeHOL := .comb [.one,.one,.one]
def fail (code : BitVec 64) : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_fail") [.const code]
def afterGuard : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def afterByte : ProgHOL 64 := match afterGuard with | .dec _ _ _ rest => rest | _ => .skip
def single : ProgHOL 64 := match afterByte with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterSingle : ProgHOL 64 := match afterByte with | .seq _ rest => rest | _ => .skip
def shortString : ProgHOL 64 := match afterSingle with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterShortString : ProgHOL 64 := match afterSingle with | .seq _ rest => rest | _ => .skip
def longString : ProgHOL 64 := match afterShortString with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterLongString : ProgHOL 64 := match afterShortString with | .seq _ rest => rest | _ => .skip
def shortList : ProgHOL 64 := match afterLongString with | .seq (.ite _ yes _) _ => yes | _ => .skip
def longList : ProgHOL 64 := match afterLongString with | .seq _ rest => rest | _ => .skip
def shortGuard : ProgHOL 64 := .ite (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "n")) (fail 3#64) .skip
def canonicalGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "n") (.const 1#64))
  (.ite (.cmp .lower (.loadByte (.op .add [localVar "p",.const 1#64])) (.const 128#64)) (fail 4#64) .skip) .skip
def shortReturn (flag : BitVec 64) : ProgHOL 64 := .return (.rstruct [.const 1#64,localVar "n",.const flag])
def lengthGuard : ProgHOL 64 := .ite (.cmp .lower (.op .sub [localVar "len",.const 1#64]) (localVar "ll")) (fail 3#64) .skip
def readArguments : List (ExpHOL 64) := [.op .add [localVar "p",.const 1#64],localVar "ll"]
def afterRead (flag : BitVec 64) : ProgHOL 64 :=
  .seq (.ite (.cmp .notLower (.const 55#64) (localVar "n")) (fail 5#64) .skip)
    (.seq (.ite (.cmp .lower (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"]) (localVar "n")) (fail 3#64) .skip)
      (.return (.rstruct [.op .add [.const 1#64,localVar "ll"],localVar "n",.const flag])))
def longCase (base flag : BitVec 64) : ProgHOL 64 := .dec (ofString "ll") .one (.op .sub [localVar "b",.const base])
  (.seq lengthGuard (.decCall (ofString "n") .one (ofString "rlp_read_length") readArguments (afterRead flag)))

set_option maxRecDepth 10000
theorem body_shape : body=.seq (.ite (.cmp .equal (localVar "len") (.const 0#64)) (fail 1#64) .skip) afterGuard := by
  simp only [body,afterGuard,fail,localVar,Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem byte_shape : afterGuard=.dec (ofString "b") .one (.loadByte (localVar "p")) afterByte := by
  simp only [afterGuard,afterByte,body,Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem cases_shape : afterByte=
    .seq (.ite (.cmp .lower (localVar "b") (.const 128#64)) single .skip)
      (.seq (.ite (.cmp .notLower (.const 183#64) (localVar "b")) shortString .skip)
        (.seq (.ite (.cmp .notLower (.const 191#64) (localVar "b")) longString .skip)
          (.seq (.ite (.cmp .notLower (.const 247#64) (localVar "b")) shortList .skip) longList))) := by
  simp only [afterByte,afterGuard,body,single,afterSingle,shortString,afterShortString,longString,afterLongString,shortList,longList,
    Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem single_shape : single=.return (.rstruct [.const 0#64,.const 1#64,.const 0#64]) := by
  simp only [single,afterByte,afterGuard,body,Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem short_string_shape : shortString=.dec (ofString "n") .one (.op .sub [localVar "b",.const 128#64])
    (.seq shortGuard (.seq canonicalGuard (shortReturn 0#64))) := by
  simp only [shortString,afterSingle,afterByte,afterGuard,body,shortGuard,canonicalGuard,shortReturn,fail,localVar,
    Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem short_list_shape : shortList=.dec (ofString "n") .one (.op .sub [localVar "b",.const 192#64])
    (.seq shortGuard (shortReturn 1#64)) := by
  simp only [shortList,afterLongString,afterShortString,afterSingle,afterByte,afterGuard,body,shortGuard,shortReturn,fail,localVar,
    Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem long_string_shape : longString=longCase 183#64 0#64 := by
  simp only [longString,afterShortString,afterSingle,afterByte,afterGuard,body,longCase,lengthGuard,readArguments,afterRead,fail,localVar,
    Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem long_list_shape : longList=longCase 247#64 1#64 := by
  simp only [longList,afterLongString,afterShortString,afterSingle,afterByte,afterGuard,body,longCase,lengthGuard,readArguments,afterRead,fail,localVar,
    Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_item_header")=some (formals,body,resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 97 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_item_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,resultShape,
    Guest.Software.guestFn_rlp_item_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.body_shape
#print axioms InitECandidate.Solver.Rlp.Header.byte_shape
#print axioms InitECandidate.Solver.Rlp.Header.cases_shape
#print axioms InitECandidate.Solver.Rlp.Header.single_shape
#print axioms InitECandidate.Solver.Rlp.Header.short_string_shape
#print axioms InitECandidate.Solver.Rlp.Header.short_list_shape
#print axioms InitECandidate.Solver.Rlp.Header.long_string_shape
#print axioms InitECandidate.Solver.Rlp.Header.long_list_shape
#print axioms InitECandidate.Solver.Rlp.Header.original_code
