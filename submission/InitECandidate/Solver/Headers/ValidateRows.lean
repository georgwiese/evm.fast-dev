import InitECandidate.Solver.Headers.ValidateSyntax
import InitECandidate.Solver.Input.HashInputFrame
import InitECandidate.Solver.Headers.FieldRowArguments

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current original header rows and their physical input extents. Every
obligation is indexed by a real row, so zero headers require no mapped
sentinel record. This contains no decoded-header or hash outcome. -/
structure Rows (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (pointers lengths : Nat→BitVec 64) (count lower upper : Nat) : Prop where
  cells : ∀ index<count,source.memory (byteAddress array (16*index))=.word (pointers index) ∧
    source.memory (byteAddress array (16*index)+8#64)=.word (lengths index)
  rowArena : ∀ index<count,AllocatedBytes.Arena (byteAddress array (16*index)) 16
  rowAligned : ∀ index<count,(byteAddress array (16*index)).toNat%8=0
  rowAfter : ∀ index<count,lower≤(byteAddress array (16*index)).toNat
  rowBefore : ∀ index<count,(byteAddress array (16*index)).toNat+16≤upper
  inputArena : ∀ index<count,AllocatedBytes.Arena (pointers index) (lengths index).toNat
  inputAfter : ∀ index<count,lower≤(pointers index).toNat
  inputBefore : ∀ index<count,(pointers index).toNat+(lengths index).toNat≤upper
  sizeBound : ∀ index<count,16*(lengths index).toNat<2^64

theorem Rows.of_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (pointers lengths : Nat→BitVec 64) (count lower upper : Nat)
    (rows : Rows source array pointers lengths count lower upper) (frame : Input.HashInput.Frame source target lower upper) :
    Rows target array pointers lengths count lower upper := by
  refine ⟨?_,rows.rowArena,rows.rowAligned,rows.rowAfter,rows.rowBefore,rows.inputArena,rows.inputAfter,rows.inputBefore,rows.sizeBound⟩
  intro index inside
  have rowWord:=frame.words (byteAddress array (16*index)) (rows.rowAfter index inside) (by have h:=rows.rowBefore index inside; omega)
  have number : (byteAddress array (16*index)+8#64).toNat=(byteAddress array (16*index)).toNat+8 := by
    exact MemoryBytes.offset_toNat _ 8 (by have h:=(rows.rowArena index inside).upper; omega)
  have lengthWord:=frame.words (byteAddress array (16*index)+8#64) (by rw [number]; have h:=rows.rowAfter index inside; omega)
    (by rw [number]; have h:=rows.rowBefore index inside; omega)
  exact ⟨rowWord.trans (rows.cells index inside).1,lengthWord.trans (rows.cells index inside).2⟩

/-- Both actual decode_header arguments are loaded from the same reached
row, with mapping derived from that row's physical allocation. -/
theorem Rows.read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (pointers lengths : Nat→BitVec 64) (count lower upper index : Nat)
    (rows : Rows source array pointers lengths count lower upper) (inside : index<count)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some (Rlp.Header.values (pointers index) (lengths index)) := by
  have rowEq : Rlp.Slices.row array (BitVec.ofNat 64 index)=byteAddress array (16*index) := by
    simp [Rlp.Slices.row,byteAddress,BitVec.ofNat_mul,Nat.mul_comm]
  have first:=AllocatedBytes.word_mapped source (byteAddress array (16*index)) 16 0 domain (rows.rowArena index inside) (by decide) (rows.rowAligned index inside) (by decide)
  have second:=AllocatedBytes.word_mapped source (byteAddress array (16*index)) 16 8 domain (rows.rowArena index inside) (by decide) (rows.rowAligned index inside) (by decide)
  have fields:=rows.cells index inside
  have result:=Field.arguments_read source array (BitVec.ofNat 64 index) (pointers index) (lengths index) arrayCell indexCell
    (by rw [rowEq]; simpa [byteAddress] using first) (by rw [rowEq]; exact second) (by rw [rowEq]; exact fields.1) (by rw [rowEq]; exact fields.2)
  exact result

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.Rows.of_frame
#print axioms InitECandidate.Solver.Headers.Validate.Rows.read
