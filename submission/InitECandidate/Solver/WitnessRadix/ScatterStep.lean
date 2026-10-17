import InitECandidate.Solver.WitnessRadix.ScatterBody
import InitECandidate.Solver.WitnessRadix.CountStep

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem post_digit {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64) (selected : Bool)
    (agrees : digit = 0#64 ↔ selected = false) :
    post source dst digit ordinal zeroCursor oneCursor index =
      post source dst (if selected then 1#64 else 0#64) ordinal zeroCursor oneCursor index := by
  cases bit : selected with
  | false => simp [post, agrees.mpr bit]
  | true =>
      have notZero : digit ≠ 0#64 := by intro eq; have wrong := agrees.mp eq; simp [bit] at wrong
      simp [post, notZero]

theorem iteration {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src dst start index keys ordinal zeroCursor oneCursor : BitVec 64)
    (position : Nat) (key : ByteKeys.Key) (inside : position < 256)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word zeroCursor)))
    (oneLocal : source.locals.lookup (ofString "one_cursor") = some (.val (.word oneCursor)))
    (mapped : source.memaddrs (BuildCopy.row src start index))
    (stored : source.memory (BuildCopy.row src start index) = .word ordinal)
    (view : MemoryBytes.ByteView source (keys + ordinal * 32#64) key)
    (destinationMapped : source.memaddrs
      (dst + (if ByteKeys.bit key position then oneCursor else zeroCursor) * 8#64)) :
    evaluateHOLFiniteState source body =
      (none, post source dst (if ByteKeys.bit key position then 1#64 else 0#64)
        ordinal zeroCursor oneCursor index) := by
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
  let digit := WordBits.digit (BitVec.ofNat 8 byte.toNat) (BitVec.ofNat 64 position)
  have readDigit := CountProgram.digit_read ordState keys ordinal (BitVec.ofNat 64 position) byte
    keys' ordinal' bit' loaded
  have choose : (if digit = 0#64 then zeroCursor else oneCursor) =
      (if ByteKeys.bit key position then oneCursor else zeroCursor) := by
    cases bit : ByteKeys.bit key position with
    | false => change (if digit = 0#64 then zeroCursor else oneCursor) = zeroCursor; rw [if_pos (selected.mpr bit)]
    | true =>
        have notZero : digit ≠ 0#64 := by intro eq; have wrong := selected.mp eq; simp [bit] at wrong
        simp only [↓reduceIte, if_neg notZero]
  have destination : source.memaddrs (dst + (if digit = 0#64 then zeroCursor else oneCursor) * 8#64) := by
    rw [choose]
    exact destinationMapped
  have result := body_execute source dst digit ordinal zeroCursor oneCursor index
    (CountProgram.ordinal_read source src start index ordinal srcLocal startLocal indexLocal mapped stored)
    readDigit dstLocal zeroLocal oneLocal indexLocal destination
  rw [result, post_digit source dst digit ordinal zeroCursor oneCursor index _ selected]

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.iteration
