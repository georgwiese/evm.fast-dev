import InitECandidate.Solver.Input.RlpLength.BlockProgram
import InitECandidate.Solver.Input.RlpLength.BytesSizeCall

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionLoop : ProgHOL 64 := ((loops body)[0]?).getD .skip
def txTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "ntx")
def txAddress : ExpHOL 64 := .op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64]]
def txLengthExpression : ExpHOL 64 := .load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64])
def txFirstExpression : ExpHOL 64 := .loadByte (.load .one txAddress)
def txReadFirst : ProgHOL 64 := .ite (.cmp .notEqual (localVar "n") (.const 0#64))
  (.assign .local (ofString "fb") txFirstExpression) .skip
def txWrapCondition : ExpHOL 64 := .cmp .notEqual (.const 0#64)
  (.op .or [.cmp .equal (localVar "n") (.const 0#64),.cmp .lower (localVar "fb") (.const 192#64)])
def txWrap : ProgHOL 64 := .ite txWrapCondition
  (.call (some (some (.local,ofString "el"),none)) (ofString "rlp_bytes_encoded_len") [localVar "fb",localVar "n"]) .skip
def txSumExpression : ExpHOL 64 := .op .add [localVar "tl",localVar "el"]
def txAdd : ProgHOL 64 := .seq (.assign .local (ofString "tl") txSumExpression) (.assign .local (ofString "i") incrementExpression)
def txAfterFirst : ProgHOL 64 := .dec (ofString "el") .one (localVar "n") (.seq txWrap txAdd)
def txAfterLength : ProgHOL 64 := .dec (ofString "fb") .one (.const 0#64) (.seq txReadFirst txAfterFirst)
def txBody : ProgHOL 64 := .dec (ofString "n") .one txLengthExpression txAfterLength

theorem transaction_loop_shape : transactionLoop=.while txTest txBody := by
  simp only [transactionLoop,loops,body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    txTest,txBody,txLengthExpression,txAfterLength,txReadFirst,txFirstExpression,txAddress,txAfterFirst,txWrap,txWrapCondition,txAdd,txSumExpression,incrementExpression,localVar]

def txStep (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) :=
  bind (bind {source with clock:=source.clock-paid} "tl" (BitVec.ofNat 64 (sum+encoded))) "i" (BitVec.ofNat 64 (index+1))

theorem wrap_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64)
    (fb : source.locals.lookup (ofString "fb")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n))) :
    eval source txWrapCondition=some (.val (.word (if n=0#64 ∨ first.toNat<192 then 1#64 else 0#64))) := by
  by_cases zero : n=0#64 <;> by_cases small : first.toNat<192
  all_goals simp [eval,txWrapCondition,localVar,evalHOLExact,evalListHOLExact,toExact,fb,len,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,zero,small,valueIsWord,valueWord,wordOpHOL,wordOp]
  all_goals decide

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.transaction_loop_shape
#print axioms InitECandidate.Solver.Input.RlpLength.Block.wrap_read
