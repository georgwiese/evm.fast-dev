import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Program
import InitECandidate.Solver.Input.CurrentTable.KeyBits

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual physical current-key bytes, independent of the historical
Patricia bit-order convention or any future successful helper execution. -/
def ByteView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (key : KeyBits.Key) : Prop :=
  ∀ index : Fin 32,@panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (pointer+BitVec.ofNat 64 index.val) = some (UInt8.ofNat (key index).toNat)

theorem ByteView.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} {key : KeyBits.Key} (view : ByteView source pointer key)
    (frame : LocalEffects.erase target = LocalEffects.erase source) : ByteView target pointer key := by
  have memory := LocalEffects.memory_of_erase source target frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  have endian := congrArg PanSemStateFiniteExact.be frame
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  intro index
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 index.val))
  all_goals simpa [panMemLoadByteHOL,memory,domain,endian,mapped] using view index

theorem widened_byte (byte : BitVec 8) :
    BitVec.ofNat 64 (UInt8.ofNat byte.toNat).toNat = byte.setWidth 64 := by
  have bounded := byte.isLt
  have natural : (UInt8.ofNat byte.toNat).toNat = byte.toNat := by
    simp [UInt8.toNat_ofNat',Nat.mod_eq_of_lt bounded]
  rw [natural]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_setWidth_of_le (by decide),Nat.mod_eq_of_lt (by omega)]

theorem byte_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (pointer : BitVec 64) (index : Nat) (byte : BitVec 8)
    (pointerCell : source.locals.lookup (ofString name) = some (.val (.word pointer)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 index) = some (UInt8.ofNat byte.toNat)) :
    eval source (.loadByte (.op .add [localVar name,localVar "i"])) =
      some (.val (.word (byte.setWidth 64))) := by
  simp [eval,evalHOLExact,evalListHOLExact,localVar,pointerCell,indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,loaded,widened_byte]

/-- The byte xor read by the unchanged outer body comes from these actual
physical loads. Memory errors remain possible in every other entry. -/
theorem read_x (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key) (index : Fin 32)
    (aCell : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bCell : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index.val))))
    (aView : ByteView source a left) (bView : ByteView source b right) :
    eval source readX = some (.val (.word ((left index ^^^ right index).setWidth 64))) := by
  have l := byte_read source "a" a index.val (left index) aCell indexCell (aView index)
  have r := byte_read source "b" b index.val (right index) bCell indexCell (bView index)
  simp only [eval] at l r ⊢
  rw [readX,evalHOLExact]
  simp only [evalListHOLExact,l,r]
  simp [valueIsWord,valueWord,wordOpHOL,wordOp]

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteView.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.read_x
