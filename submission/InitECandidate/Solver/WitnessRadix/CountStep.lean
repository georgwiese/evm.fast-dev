import InitECandidate.Solver.WitnessRadix.CountBody

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem ordinal_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start index ordinal : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (BuildCopy.row src start index))
    (stored : source.memory (BuildCopy.row src start index) = .word ordinal) :
    eval source ordinalExpression = some (.val (.word ordinal)) := by
  classical
  have address := BuildCopy.address_read source "src" src start index srcLocal startLocal indexLocal
  simp only [eval] at address
  simp only [eval, ordinalExpression, evalHOLExact, address, isWfShapeExactHOL,
    memLoadHOLExact, toExact, mapped, stored, ↓reduceIte]

/-- Concrete mapped ordinal/key bytes determine the exact counting iteration.
No evaluation or comparison success is assumed. -/
theorem iteration {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start index keys ordinal zeros : BitVec 64) (position : Nat) (key : ByteKeys.Key)
    (inside : position < 256)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (mapped : source.memaddrs (BuildCopy.row src start index))
    (stored : source.memory (BuildCopy.row src start index) = .word ordinal)
    (view : MemoryBytes.ByteView source (keys + ordinal * 32#64) key) :
    evaluateHOLFiniteState source body =
      (none, counterPost source (if ByteKeys.bit key position then 1#64 else 0#64) zeros index) := by
  classical
  let ordState := bind source "ordinal" ordinal
  have names : ofString "ordinal" ≠ ofString "keys" ∧ ofString "ordinal" ≠ ofString "bit" := by decide
  have keys' : ordState.locals.lookup (ofString "keys") = some (.val (.word keys)) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, names.1, keysLocal]
  have bit' : ordState.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, names.2, bitLocal]
  have ordinal' : ordState.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have view' := MemoryBytes.byteView_of_fields source ordState rfl rfl rfl _ _ view
  obtain ⟨byte, loaded, selected⟩ := QueryMemory.query_digit ordState (keys + ordinal * 32#64)
    key position inside view'
  have readDigit := digit_read ordState keys ordinal (BitVec.ofNat 64 position) byte keys' ordinal' bit' loaded
  have result := body_execute source ordinal
    (WordBits.digit (BitVec.ofNat 8 byte.toNat) (BitVec.ofNat 64 position)) zeros index
    (ordinal_read source src start index ordinal srcLocal startLocal indexLocal mapped stored)
    readDigit zerosLocal indexLocal
  rw [result]
  cases bit : ByteKeys.bit key position with
  | false =>
      have zero := selected.mpr bit
      simp only [bit, Bool.false_eq_true, ↓reduceIte, counterPost, zero]
  | true =>
      have nonzero : WordBits.digit (BitVec.ofNat 8 byte.toNat) (BitVec.ofNat 64 position) ≠ 0#64 := by
        intro eq
        have wrong := selected.mp eq
        simp [bit] at wrong
      simp only [bit, ↓reduceIte, counterPost, if_neg nonzero]
      rw [if_neg (by decide)]

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.iteration
