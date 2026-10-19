import InitECandidate.Solver.Rlp.SlicesStoreFrame
import InitECandidate.Solver.Rlp.ListItems

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

def Records (memory : BitVec 64 → HolWordLab 64) (array pointer : BitVec 64) : List ListItem → Prop
  | [] => True
  | item::items => memory array=.word pointer ∧ memory (array+8#64)=.word item.total ∧
      Records memory (array+16#64) (pointer+item.total) items

def Window (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Prop :=
  ∀ query : BitVec 64,query.toNat<lower ∨ upper≤query.toNat → target.memory query=source.memory query

theorem Window.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Window source source lower upper := by
  intro query outside
  rfl

theorem Window.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (first : Window source middle lower upper) (second : Window middle target lower upper) : Window source target lower upper := by
  intro query outside
  exact (second query outside).trans (first query outside)

theorem Window.mono (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper widerLower widerUpper : Nat)
    (frame : Window source target lower upper) (lo : widerLower≤lower) (hi : upper≤widerUpper) : Window source target widerLower widerUpper := by
  intro query outside
  apply frame query
  rcases outside with before|after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem stores_window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset size count : BitVec 64)
    (inside : index.toNat<count.toNat) (fits : array.toNat+16*count.toNat<2^64) :
    Window source (storesPost source pointer array index offset size)
      (array.toNat+16*index.toNat) (array.toNat+16*(index.toNat+1)) := by
  have firstNumber := row_number array index (by omega)
  have secondNumber := row_length_number array index count inside fits
  intro query outside
  change (written source pointer array index offset size).memory query=source.memory query
  apply written_away
  · intro same
    have number := congrArg BitVec.toNat same
    rw [firstNumber] at number
    rcases outside with before|after <;> omega
  · intro same
    have number := congrArg BitVec.toNat same
    rw [secondNumber] at number
    rcases outside with before|after <;> omega

theorem row_next (array index : BitVec 64) : row array (index+1#64)=row array index+16#64 := by
  simp [row,BitVec.add_mul,BitVec.add_assoc]

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Window.refl
#print axioms InitECandidate.Solver.Rlp.Slices.Window.trans
#print axioms InitECandidate.Solver.Rlp.Slices.Window.mono
#print axioms InitECandidate.Solver.Rlp.Slices.stores_window
#print axioms InitECandidate.Solver.Rlp.Slices.row_next
