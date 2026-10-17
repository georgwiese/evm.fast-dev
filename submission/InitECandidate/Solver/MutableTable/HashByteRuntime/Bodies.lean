import InitECandidate.Solver.MutableTable.HashByteRuntime.Program
import InitECandidate.Solver.Input.Scalar64

namespace InitECandidate.Solver.MutableTable.HashByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def blockWord (bytes : Nat → UInt8) (index : Nat) : BitVec 64 :=
  Input.WordCodec.word8 (BitVec.ofNat 64 (bytes index).toNat) (BitVec.ofNat 64 (bytes (index + 1)).toNat)
    (BitVec.ofNat 64 (bytes (index + 2)).toNat) (BitVec.ofNat 64 (bytes (index + 3)).toNat)
    (BitVec.ofNat 64 (bytes (index + 4)).toNat) (BitVec.ofNat 64 (bytes (index + 5)).toNat)
    (BitVec.ofNat 64 (bytes (index + 6)).toNat) (BitVec.ofNat 64 (bytes (index + 7)).toNat)
def blockNext {F : Type} (source : PanSemStateFiniteExact 64 F) (index : Nat) (hash word : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "w" word) "h" (hash ^^^ word)) "i" (BitVec.ofNat 64 index + 8#64)
def byteNext {F : Type} (source : PanSemStateFiniteExact 64 F) (index : Nat) (hash : BitVec 64) (byte : UInt8) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "h" (hash ^^^ BitVec.ofNat 64 byte.toNat)) "i" (BitVec.ofNat 64 index + 1#64)
def finalWord (hash : BitVec 64) : BitVec 64 :=
  let h := (hash ^^^ (hash >>> (32 : Nat))) * 1099511628211#64
  h ^^^ (h >>> (29 : Nat))

theorem Inputs.block_next {F : Type} {source : PanSemStateFiniteExact 64 F} {pointer : BitVec 64} {length : Nat} {bytes : Nat → UInt8}
    (inputs : Inputs source pointer length bytes) (index : Nat) (hash word : BitVec 64) :
    Inputs (blockNext source index hash word) pointer length bytes := by
  constructor
  · exact (bind_lookup_other _ "i" "p" _ (by decide)).trans ((bind_lookup_other _ "h" "p" _ (by decide)).trans
      ((bind_lookup_other _ "w" "p" _ (by decide)).trans inputs.pointerLocal))
  · exact (bind_lookup_other _ "i" "key_len" _ (by decide)).trans ((bind_lookup_other _ "h" "key_len" _ (by decide)).trans
      ((bind_lookup_other _ "w" "key_len" _ (by decide)).trans inputs.lengthLocal))
  · exact ⟨word, (bind_lookup_other _ "i" "w" _ (by decide)).trans ((bind_lookup_other _ "h" "w" _ (by decide)).trans (bind_lookup_same _ _ _))⟩
  · exact inputs.reads

theorem Inputs.byte_next {F : Type} {source : PanSemStateFiniteExact 64 F} {pointer : BitVec 64} {length : Nat} {bytes : Nat → UInt8}
    (inputs : Inputs source pointer length bytes) (index : Nat) (hash : BitVec 64) (byte : UInt8) :
    Inputs (byteNext source index hash byte) pointer length bytes := by
  constructor
  · exact (bind_lookup_other _ "i" "p" _ (by decide)).trans ((bind_lookup_other _ "h" "p" _ (by decide)).trans inputs.pointerLocal)
  · exact (bind_lookup_other _ "i" "key_len" _ (by decide)).trans ((bind_lookup_other _ "h" "key_len" _ (by decide)).trans inputs.lengthLocal)
  · obtain ⟨oldWord, oldTyped⟩ := inputs.wTyped
    exact ⟨oldWord, (bind_lookup_other _ "i" "w" _ (by decide)).trans ((bind_lookup_other _ "h" "w" _ (by decide)).trans oldTyped)⟩
  · exact inputs.reads

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- Every real byte load and fold in the original eight-byte hash body. -/
theorem block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer hash : BitVec 64) (length index : Nat)
    (bytes : Nat → UInt8) (inputs : Inputs source pointer length bytes)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word hash))) (inside : index + 8 ≤ length) :
    evaluateHOLFiniteState source blockBody = (none, blockNext source index hash (blockWord bytes index)) := by
  classical
  obtain ⟨oldWord, wLocal⟩ := inputs.wTyped
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c = BitVec.or a (BitVec.or b c) := BitVec.or_assoc a b c
  have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + BitVec.ofNat 64 index) = some (bytes (index + 0)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 0) (by omega)
  have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 1#64)) = some (bytes (index + 1)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 1) (by omega)
  have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 2#64)) = some (bytes (index + 2)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 2) (by omega)
  have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 3#64)) = some (bytes (index + 3)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 3) (by omega)
  have r4 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 4#64)) = some (bytes (index + 4)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 4) (by omega)
  have r5 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 5#64)) = some (bytes (index + 5)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 5) (by omega)
  have r6 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 6#64)) = some (bytes (index + 6)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 6) (by omega)
  have r7 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + (BitVec.ofNat 64 index + 7#64)) = some (bytes (index + 7)) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero] using inputs.reads (index + 7) (by omega)
  simp [blockBody, program, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite,
    setKvarHOLFinite, lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE, inputs.pointerLocal,
    current, hLocal, wLocal, foldXor, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
    shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, blockNext, WitnessRadix.QueryBranch.bind, blockWord,
    Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
    r0, r1, r2, r3, r4, r5, r6, r7,
    show ofString "h" ≠ ofString "w" from by decide, show ofString "i" ≠ ofString "h" from by decide,
    show ofString "i" ≠ ofString "w" from by decide,
    show ofString "h" ≠ ofString "i" from by decide, show ofString "w" ≠ ofString "i" from by decide,
    show ofString "w" ≠ ofString "h" from by decide]
  all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
  all_goals rfl

/-- Original trailing-byte hash body, with its real load and index advance. -/
theorem byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer hash : BitVec 64) (length index : Nat)
    (bytes : Nat → UInt8) (inputs : Inputs source pointer length bytes)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word hash))) (inside : index < length) :
    evaluateHOLFiniteState source byteBody = (none, byteNext source index hash (bytes index)) := by
  have read := inputs.reads index inside
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  simp [byteBody, tailProgram, program, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite,
    setKvarHOLFinite, lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE, inputs.pointerLocal,
    current, hLocal, foldXor, valueIsWord, valueWord, wordOpHOL, wordOp, read,
    shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, byteNext, WitnessRadix.QueryBranch.bind,
    show ofString "h" ≠ ofString "i" from by decide]

/-- Actual avalanche operations and final hash return; no body clocks. -/
theorem finish_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (hash : BitVec 64)
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word hash))) :
    evaluateHOLFiniteState source finish = (some (.returned (.val (.word (finalWord hash)))), emptyLocalsHOLFinite source) := by
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  simp [finish, tailProgram, program, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite,
    setKvarHOLFinite, lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
    hLocal, foldXor, valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, panOpHOL,
    shapeOfHOLExact, shapeEqHOL, sizeOfShapeWithContextHOL, fixClockHOLFinite, finalWord, emptyLocalsHOLFinite]

end InitECandidate.Solver.MutableTable.HashByteRuntime

#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.Inputs.block_next
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.Inputs.byte_next
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.block_execute
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.byte_execute
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.finish_execute
