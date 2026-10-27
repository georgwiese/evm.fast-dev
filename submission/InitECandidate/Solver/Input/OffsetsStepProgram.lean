import InitECandidate.Solver.Input.OffsetsProgram

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def condition : ExpHOL 64 := .cmp .less (localVar "i") (localVar "n")
def cellAddress : ExpHOL 64 := .op .add [localVar "offs",.panop .mul [localVar "i",.const 8#64]]
def previous : ExpHOL 64 := .load .one (.op .sub [cellAddress,.const 8#64])
def fail (code : BitVec 64) : ProgHOL 64 := .call (some (none,none)) (ofString "ssz_fail") [.const code]
def rangeTest : ExpHOL 64 := .cmp .notEqual (.const 0#64)
  (.op .or [.cmp .lower (localVar "o") (localVar "fixed"),.cmp .lower (localVar "len") (localVar "o")])
def rangeGuard : ProgHOL 64 := .ite rangeTest (fail 10#64) .skip
def hasPrevious : ExpHOL 64 := .cmp .less (.const 0#64) (localVar "i")
def orderTest : ExpHOL 64 := .cmp .lower (localVar "o") previous
def orderGuard : ProgHOL 64 := .ite hasPrevious (.ite orderTest (fail 11#64) .skip) .skip
def increment : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") 1#64)
def checks : ProgHOL 64 := .seq rangeGuard (.seq orderGuard increment)

theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,body,loopBody,Guest.Software.guestFn_ssz_check_offsets,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,condition,localVar]

theorem loop_body_shape : loopBody=.dec (ofString "o") .one (.load .one cellAddress) checks := by
  simp only [loopBody,loop,body,Guest.Software.guestFn_ssz_check_offsets,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    cellAddress,checks,rangeGuard,rangeTest,orderGuard,hasPrevious,orderTest,previous,fail,increment,localVar,addConst,Option.map_none]

theorem cell_address_read {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (index : Nat)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source cellAddress=some (.val (.word (pointer+BitVec.ofNat 64 (8*index)))) := by
  classical
  simp [eval,cellAddress,localVar,evalHOLExact,evalListHOLExact,toExact,pointerLocal,indexLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index count : Nat)
    (indexSmall : index≤8) (countSmall : count≤8)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    @evalHOLFinite 64 F _ source (fun address=>Classical.propDecidable (source.memaddrs address)) condition=
      some (.val (.word (if index<count then 1#64 else 0#64))) := by
  have encodedI : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have encodedN : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have i63 : index<9223372036854775808 := by omega
  have n63 : count<9223372036854775808 := by omega
  simp [condition,localVar,evalHOLFinite,evalHOLExact,toExact,indexLocal,countLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
    encodedI,encodedN,i63,n63]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.loop_shape
#print axioms InitECandidate.Solver.Input.Offsets.loop_body_shape
#print axioms InitECandidate.Solver.Input.Offsets.cell_address_read
#print axioms InitECandidate.Solver.Input.Offsets.condition_read
