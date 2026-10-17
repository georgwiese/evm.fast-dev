import InitECandidate.Solver.WitnessRadix.MemeqByteReads
import InitECandidate.Solver.WitnessRadix.ByteRegion

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

abbrev indexed := @Memeq32.indexed
abbrev condition8 := Memeq32.condition8
abbrev condition1 := Memeq32.condition1
abbrev blockBody := Memeq32.byteBodies.1
abbrev byteBody := Memeq32.byteBodies.2

def increment1 : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") 1#64)
def byteChecks (left right : UInt8) : List CompareChain.Comparison :=
  [⟨Memeq32.byteAt "a" 0, Memeq32.byteAt "b" 0, BitVec.ofNat 64 left.toNat, BitVec.ofNat 64 right.toNat⟩]

theorem byte_body_shape (left right : UInt8) : byteBody = CompareChain.prefixChecks (byteChecks left right) increment1 := by
  simp only [byteBody, Memeq32.byteBodies, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, CompareChain.prefixChecks,
    CompareChain.returned, byteChecks, Memeq32.byteAt, increment1, addConst, localVar, ↓reduceIte]

structure Inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length : Nat)
    (left right : Nat → UInt8) : Prop where
  aLocal : source.locals.lookup (ofString "a") = some (.val (.word a))
  bLocal : source.locals.lookup (ofString "b") = some (.val (.word b))
  lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))
  leftRead : ∀ index < length, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (a + BitVec.ofNat 64 index) = some (left index)
  rightRead : ∀ index < length, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (b + BitVec.ofNat 64 index) = some (right index)

theorem Inputs.indexed {F : Type} {source : PanSemStateFiniteExact 64 F} {a b : BitVec 64} {length : Nat}
    {left right : Nat → UInt8} (inputs : Inputs source a b length left right) (clock index : Nat) :
    Inputs (Memeq32.indexed source clock index) a b length left right :=
  ⟨(bind_lookup_other _ "i" "a" _ (by decide)).trans inputs.aLocal,
   (bind_lookup_other _ "i" "b" _ (by decide)).trans inputs.bLocal,
   (bind_lookup_other _ "i" "n" _ (by decide)).trans inputs.lengthLocal,
   inputs.leftRead, inputs.rightRead⟩

theorem condition8_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length ≤ 64) (inside : index ≤ length)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source condition8 = some (.val (.word (if index + 8 ≤ length then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat = index := by change index % 2 ^ 64 = index; exact Nat.mod_eq_of_lt (by omega)
  have nNumber : (BitVec.ofNat 64 length).toNat = length := by change length % 2 ^ 64 = length; exact Nat.mod_eq_of_lt (by omega)
  have sumNumber : (BitVec.ofNat 64 index + 8#64).toNat = index + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [iNumber]; change index + 8 < 2 ^ 64; omega), iNumber]
    rfl
  have comparison : (BitVec.ofNat 64 length < BitVec.ofNat 64 index + 8#64) ↔ length < index + 8 := by
    change (BitVec.ofNat 64 length).toNat < (BitVec.ofNat 64 index + 8#64).toNat ↔ _
    rw [nNumber, sumNumber]
  by_cases active : index + 8 ≤ length
  · have wordNotLower : ¬ BitVec.ofNat 64 length < BitVec.ofNat 64 index + 8#64 := by rw [comparison]; omega
    simp [eval, condition8, Memeq32.condition8, addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordNotLower]
  · have wordLower : BitVec.ofNat 64 length < BitVec.ofNat 64 index + 8#64 := by rw [comparison]; omega
    simp [eval, condition8, Memeq32.condition8, addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordLower]

theorem condition1_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length ≤ 64) (inside : index ≤ length)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source condition1 = some (.val (.word (if index < length then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat = index := by change index % 2 ^ 64 = index; exact Nat.mod_eq_of_lt (by omega)
  have nNumber : (BitVec.ofNat 64 length).toNat = length := by change length % 2 ^ 64 = length; exact Nat.mod_eq_of_lt (by omega)
  have comparison : (BitVec.ofNat 64 index < BitVec.ofNat 64 length) ↔ index < length := by
    change (BitVec.ofNat 64 index).toNat < (BitVec.ofNat 64 length).toNat ↔ _
    rw [iNumber, nNumber]
  simp [eval, condition1, Memeq32.condition1, localVar, evalHOLExact, toExact, current, lengthLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, comparison]

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.byte_body_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.Inputs.indexed
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.condition8_read
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.condition1_read
