import InitECandidate.Solver.WitnessRadix.MemeqBytes

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem eval_byteAt {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : String) (pointer index : BitVec 64) (offset : Nat) (byte : UInt8)
    (argument : state.locals.lookup (ofString name) = some (.val (.word pointer)))
    (current : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (pointer + index + BitVec.ofNat 64 offset) = some byte) :
    eval state (byteAt name offset) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  classical
  have loaded' : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (pointer + (index + BitVec.ofNat 64 offset)) = some byte := by
    simpa only [BitVec.add_assoc] using loaded
  by_cases zero : offset = 0
  · subst offset
    have read : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be
        (pointer + index) = some byte := by simpa using loaded
    simp [eval, byteAt, localVar, evalHOLExact, evalListHOLExact, toExact, argument,
      current, valueIsWord, valueWord, wordOpHOL, wordOp, read]
  · simp [eval, byteAt, zero, localVar, evalHOLExact, evalListHOLExact, toExact,
      argument, current, valueIsWord, valueWord, wordOpHOL, wordOp, loaded']

theorem eval_condition8 {F : Type} (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (current : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    eval state condition8 = some (.val (.word (if 32#64 < index + 8#64 then 0#64 else 1#64))) := by
  classical
  by_cases low : 32#64 < index + 8#64
  all_goals simp [eval, condition8, addConst, localVar, evalHOLExact, evalListHOLExact,
    toExact, current, length, valueIsWord, valueWord, wordOpHOL, wordOp, low,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem eval_condition1_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (current : state.locals.lookup (ofString "i") = some (.val (.word 32#64)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    eval state condition1 = some (.val (.word 0#64)) := by
  classical
  simp [eval, condition1, localVar, evalHOLExact, toExact, current, length,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.eval_byteAt
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.eval_condition8
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.eval_condition1_done
