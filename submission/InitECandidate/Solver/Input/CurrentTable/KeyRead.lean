import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.BitFacts
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Program

namespace InitECandidate.Solver.Input.CurrentTable.KeyRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def byteIndex (name : String) : ExpHOL 64 := .shift .lsr (localVar name) (.const 3#64)
def digitIndex (name : String) : ExpHOL 64 := .op .and [localVar name,.const 7#64]
def amount (name : String) : ExpHOL 64 := .op .sub [.const 7#64,digitIndex name]
def loaded (keyName positionName : String) : ExpHOL 64 := .loadByte (.op .add [localVar keyName,byteIndex positionName])
def mask (keyName positionName : String) : ExpHOL 64 := .op .and [.shift .lsr (loaded keyName positionName) (amount positionName),.const 1#64]

theorem index_word (position : Nat) (inside : position < 256) :
    (BitVec.ofNat 64 position >>> 3) = BitVec.ofNat 64 (position/8) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

theorem digit_word (position : Nat) (inside : position < 256) :
    AndOp.and (BitVec.ofNat 64 position) 7#64 = BitVec.ofNat 64 (position%8) := by
  change (BitVec.ofNat 64 position &&& 7#64) = _
  apply BitVec.eq_of_toNat_eq
  have small : position < 2^64 := by omega
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  change position &&& 7 = (position%8)%18446744073709551616
  rw [show 7 = 2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (position : Nat) (inside : position < 256)
    (cell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source (byteIndex name) = some (.val (.word (BitVec.ofNat 64 (position/8)))) := by
  simp [byteIndex,eval,evalHOLExact,localVar,cell,wordShiftHOL]
  exact index_word position inside

theorem digit_index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (position : Nat) (inside : position < 256)
    (cell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source (digitIndex name) = some (.val (.word (BitVec.ofNat 64 (position%8)))) := by
  have oneMask : AndOp.and (7#64 : BitVec 64) 18446744073709551615#64 = 7#64 := by decide
  simp [digitIndex,eval,evalHOLExact,evalListHOLExact,localVar,cell,valueIsWord,valueWord,
    wordOpHOL,wordOp,oneMask,digit_word position inside]

theorem amount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (position : Nat) (inside : position < 256)
    (cell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source (amount name) = some (.val (.word (BitVec.ofNat 64 (7-position%8)))) := by
  have digit := digit_index_read source name position inside cell
  have numeral : (BitVec.ofNat 64 (position%8)).toNat = position%8 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : 7#64-BitVec.ofNat 64 (position%8) = BitVec.ofNat 64 (7-position%8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 (position%8)).toNat ≤ 7; rw [numeral]; omega),numeral]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [eval] at digit ⊢
  rw [amount,evalHOLExact]
  simp only [evalListHOLExact,digit]
  simp [evalHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

theorem loaded_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (keyName positionName : String) (pointer : BitVec 64) (key : KeyBits.Key)
    (position : Nat) (inside : position < 256)
    (keyCell : source.locals.lookup (ofString keyName) = some (.val (.word pointer)))
    (positionCell : source.locals.lookup (ofString positionName) = some (.val (.word (BitVec.ofNat 64 position))))
    (view : FirstDiff.ByteView source pointer key) :
    eval source (loaded keyName positionName) =
      some (.val (.word ((key (Fin.ofNat 32 (position/8))).setWidth 64))) := by
  have index := byte_index_read source positionName position inside positionCell
  have observed := view (Fin.ofNat 32 (position/8))
  rw [KeyBits.byte_index position inside] at observed
  have addressRead : eval source (.op .add [localVar keyName,byteIndex positionName]) =
      some (.val (.word (pointer+BitVec.ofNat 64 (position/8)))) := by
    simp only [eval] at index ⊢
    rw [evalHOLExact]
    simp [evalListHOLExact,index,evalHOLExact,localVar,keyCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [loaded,eval] at addressRead ⊢
  rw [evalHOLExact,addressRead]
  simp [observed,FirstDiff.widened_byte]

/-- The actual key-bit mask used by both Patricia traversals. -/
theorem mask_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (keyName positionName : String) (pointer : BitVec 64) (key : KeyBits.Key)
    (position : Nat) (inside : position < 256)
    (keyCell : source.locals.lookup (ofString keyName) = some (.val (.word pointer)))
    (positionCell : source.locals.lookup (ofString positionName) = some (.val (.word (BitVec.ofNat 64 position))))
    (view : FirstDiff.ByteView source pointer key) :
    eval source (mask keyName positionName) = some (.val (.word (if KeyBits.bit key position then 1#64 else 0#64))) := by
  have bytes := loaded_read source keyName positionName pointer key position inside keyCell positionCell view
  have shift := amount_read source positionName position inside positionCell
  have small : (BitVec.ofNat 64 (7-position%8)).toNat = 7-position%8 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shifted : eval source (.shift .lsr (loaded keyName positionName) (amount positionName)) =
      some (.val (.word ((key (Fin.ofNat 32 (position/8))).setWidth 64 >>> (7-position%8)))) := by
    simp only [eval] at bytes shift ⊢
    rw [evalHOLExact]
    simp [bytes,shift,wordShiftHOL,small,show ¬(7-position%8 ≠ 0 ∧ 64 ≤ 7-position%8) from by omega]
  have oneMask : AndOp.and (1#64 : BitVec 64) 18446744073709551615#64 = 1#64 := by decide
  have observedMask : AndOp.and ((key (Fin.ofNat 32 (position/8))).setWidth 64 >>> (7-position%8)) 1#64 =
      (if KeyBits.bit key position then 1#64 else 0#64) := by
    have digit : ((key (Fin.ofNat 32 (position/8))).setWidth 64).getLsbD (7-position%8) = KeyBits.bit key position := by
      simp [KeyBits.bit,BitVec.getLsbD_setWidth,show 7-position%8 < 64 from by omega]
    rw [←digit]
    exact FirstDiff.masked_bit ((key (Fin.ofNat 32 (position/8))).setWidth 64) (7-position%8)
  simp only [eval] at shifted ⊢
  rw [mask,evalHOLExact]
  simp only [evalListHOLExact,shifted]
  simp [evalHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,oneMask,observedMask]

set_option maxRecDepth 100000 in
theorem find_test_shape : FindLeaf.keyTest = .cmp .equal (mask "key" "b") (.const 0#64) := by
  simp only [FindLeaf.keyTest,FindLeaf.branch,FindLeaf.afterBit,FindLeaf.step,FindLeaf.loop,
    FindLeaf.afterRoot,FindLeaf.afterNodes,FindLeaf.afterBits,FindLeaf.body,
    Guest.Software.guestFn_htab_find_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    mask,loaded,byteIndex,amount,digitIndex,localVar]

theorem find_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (key : KeyBits.Key) (position : Nat) (inside : position < 256)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (positionCell : source.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 position))))
    (view : FirstDiff.ByteView source pointer key) :
    eval source FindLeaf.keyTest = some (.val (.word (if KeyBits.bit key position then 0#64 else 1#64))) := by
  have bitRead := mask_read source "key" "b" pointer key position inside keyCell positionCell view
  simp only [eval] at bitRead ⊢
  rw [find_test_shape,evalHOLExact]
  simp only [bitRead]
  cases digit : KeyBits.bit key position <;>
    simp [digit,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.Input.CurrentTable.KeyRead

#print axioms InitECandidate.Solver.Input.CurrentTable.KeyRead.index_word
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyRead.mask_read

#print axioms InitECandidate.Solver.Input.CurrentTable.KeyRead.find_test_read
