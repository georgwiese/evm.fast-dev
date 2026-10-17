import InitECandidate.Solver.MutableTable.HashSizedExecution
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.MutableTable.HashByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def program : ProgHOL 64 := match Hash.afterLocals with | .seq _ (.dec _ _ _ tail) => tail | _ => .skip
def front : ProgHOL 64 := match Hash.afterLocals with | .seq front _ => front | _ => .skip
def blockBody : ProgHOL 64 := match program with | .seq (.while _ body) _ => body | _ => .skip
def tailProgram : ProgHOL 64 := match program with | .seq _ tail => tail | _ => .skip
def byteBody : ProgHOL 64 := match tailProgram with | .seq (.while _ body) _ => body | _ => .skip
def finish : ProgHOL 64 := match tailProgram with | .seq _ tail => tail | _ => .skip

def condition8 : ExpHOL 64 := .cmp .notLower (localVar "key_len") (addConst (localVar "i") 8#64)
def condition1 : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "key_len")

theorem after_locals_shape : Hash.afterLocals = .seq front (.dec (ofString "i") .one (.const 0#64) program) := by
  simp only [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, front, program]

theorem program_shape : program = .seq (.while condition8 blockBody) tailProgram := by
  simp only [program, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    condition8, addConst, localVar, blockBody, tailProgram]

theorem tail_shape : tailProgram = .seq (.while condition1 byteBody) finish := by
  simp only [tailProgram, program, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    condition1, localVar, byteBody, finish]

structure Inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length : Nat) (bytes : Nat → UInt8) : Prop where
  pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer))
  lengthLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length)))
  wTyped : ∃ word, source.locals.lookup (ofString "w") = some (.val (.word word))
  reads : ∀ index < length, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + BitVec.ofNat 64 index) = some (bytes index)

theorem condition8_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length ≤ 64) (inside : index ≤ length)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length)))) :
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
    simp [eval, condition8,  addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordNotLower]
  · have wordLower : BitVec.ofNat 64 length < BitVec.ofNat 64 index + 8#64 := by rw [comparison]; omega
    simp [eval, condition8,  addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, current, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, active, wordLower]

theorem condition1_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length ≤ 64) (inside : index ≤ length)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source condition1 = some (.val (.word (if index < length then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat = index := by change index % 2 ^ 64 = index; exact Nat.mod_eq_of_lt (by omega)
  have nNumber : (BitVec.ofNat 64 length).toNat = length := by change length % 2 ^ 64 = length; exact Nat.mod_eq_of_lt (by omega)
  have comparison : (BitVec.ofNat 64 index < BitVec.ofNat 64 length) ↔ index < length := by
    change (BitVec.ofNat 64 index).toNat < (BitVec.ofNat 64 length).toNat ↔ _
    rw [iNumber, nNumber]
  simp [eval, condition1,  localVar, evalHOLExact, toExact, current, lengthLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, comparison]

end InitECandidate.Solver.MutableTable.HashByteRuntime

#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.after_locals_shape
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.program_shape
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.tail_shape
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.condition8_read
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.condition1_read
