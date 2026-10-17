import InitECandidate.Solver.WitnessRadix.WordBits
import InitECandidate.Solver.Input.RlpWrite.U256Limb
import InitECandidate.Solver.Input.RlpWrite.U256ByteLength

namespace InitECandidate.Solver.Input.RlpWrite.U256Min
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_u256_to_be_min with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",U256Value.tupleShape),(ofString "out",.one)]
def loopTest : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "len")
def position : ExpHOL 64 := .op .sub [.op .sub [localVar "len",.const 1#64],localVar "i"]
def limbIndex : ExpHOL 64 := .shift .lsr (localVar "pos") (.const 3#64)
def destination : ExpHOL 64 := .op .add [localVar "out",localVar "i"]
def shiftAmount : ExpHOL 64 := .panop .mul [.op .and [localVar "pos",.const 7#64],.const 8#64]
def byteValue : ExpHOL 64 := .op .and [.shift .lsr (localVar "l") shiftAmount,.const 255#64]
def increment : ExpHOL 64 := .op .add [localVar "i",.const 1#64]
def afterLimb : ProgHOL 64 := .seq (.storeByte destination byteValue) (.assign .local (ofString "i") increment)
def afterPosition : ProgHOL 64 := .decCall (ofString "l") .one (ofString "u256_limb") [localVar "a",limbIndex] afterLimb
def loopBody : ProgHOL 64 := .dec (ofString "pos") .one position afterPosition
def loop : ProgHOL 64 := .while loopTest loopBody
def initialized : ProgHOL 64 := .seq loop (.return (localVar "len"))
def afterLength : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) initialized

theorem body_shape : body=.decCall (ofString "len") .one (ofString "u256_byte_length") [localVar "a"] afterLength := by
  simp only [body,Guest.guestFn_u256_to_be_min,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterLength,initialized,loop,loopTest,loopBody,position,afterPosition,limbIndex,afterLimb,destination,byteValue,shiftAmount,increment,localVar]

theorem and_ones (word : BitVec 64) : AndOp.and word (18446744073709551615#64)=word := by
  change word &&& BitVec.allOnes 64=word
  exact BitVec.and_allOnes

theorem shift_amount_small (pos : BitVec 64) : ((pos &&& 7#64)*8#64).toNat<64 := by
  rw [BitVec.toNat_mul,WitnessRadix.WordBits.mask7]
  have remainder:=Nat.mod_lt pos.toNat (by decide : 0<8)
  change (pos.toNat%8*8)%2^64<64
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem byte_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pos word : BitVec 64)
    (p : source.locals.lookup (ofString "pos")=some (.val (.word pos)))
    (l : source.locals.lookup (ofString "l")=some (.val (.word word))) :
    eval source byteValue=some (.val (.word ((word >>> (((pos &&& 7#64)*8#64).toNat)) &&& 255#64))) := by
  classical
  have small:=shift_amount_small pos
  have amountRead : eval source shiftAmount=some (.val (.word ((pos &&& 7#64)*8#64))) := by
    simp [eval,shiftAmount,localVar,evalHOLExact,evalListHOLExact,toExact,p,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,and_ones]
    rfl
  have shiftedRead : eval source (.shift .lsr (localVar "l") shiftAmount)=
      some (.val (.word (word >>> (((pos &&& 7#64)*8#64).toNat)))) := by
    simp only [eval] at amountRead ⊢
    rw [evalHOLExact]
    simp only [localVar,evalHOLExact,toExact,l,amountRead]
    have valid : ¬(((pos &&& 7#64)*8#64).toNat≠0 ∧ 64≤((pos &&& 7#64)*8#64).toNat) := by omega
    simp only [wordShiftHOL,if_neg valid,Option.map_some]
  simp only [eval] at shiftedRead ⊢
  rw [byteValue,evalHOLExact]
  simp only [evalListHOLExact,shiftedRead]
  simp [evalHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,and_ones]
  rfl

theorem position_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat) (active : index<length) (small : length≤32)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source position=some (.val (.word (BitVec.ofNat 64 (length-1-index)))) := by
  have first : BitVec.ofNat 64 length-1#64=BitVec.ofNat 64 (length-1) := BitVec.ofNat_sub_ofNat_of_le length 1 (by decide) (by omega)
  have second : BitVec.ofNat 64 (length-1)-BitVec.ofNat 64 index=BitVec.ofNat 64 (length-1-index) :=
    BitVec.ofNat_sub_ofNat_of_le (length-1) index (by omega) (by omega)
  simp [eval,position,localVar,evalHOLExact,evalListHOLExact,toExact,i,n,valueIsWord,valueWord,wordOpHOL,wordOp,first,second]

end InitECandidate.Solver.Input.RlpWrite.U256Min

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.shift_amount_small
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.byte_read
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.position_read
