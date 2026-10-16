import InitECandidate.Solver.GuestWork.ZeroProgram

namespace InitECandidate.Solver.GuestWork.ZeroMemory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open Flapjack.Compiler.Encoders.Asm
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

theorem wordStoreZero {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (reg addressReg : Nat) (offset : BitVec 64)
    (zeroReg : source.regs.lookup reg = some (.word 0#64)) :
    Below (evaluate (.inst (.mem .store reg (.addr addressReg offset)), source)).2.memory source.memory := by
  cases address : wordExp source (.op .add [.var addressReg, .const offset]) with
  | none =>
    simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address] using Below.refl source.memory
  | some target =>
    by_cases domain : source.mdomain target = true
    · simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address, getVar, zeroReg,
        memStore, domain] using wordUpdate source.memory target
    · simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address, getVar, zeroReg,
        memStore, domain] using Below.refl source.memory

theorem byteStoreZero {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (reg addressReg : Nat) (offset : BitVec 64)
    (zeroReg : source.regs.lookup reg = some (.word 0#64)) :
    Below (evaluate (.inst (.mem .store8 reg (.addr addressReg offset)), source)).2.memory source.memory := by
  cases address : wordExp source (.op .add [.var addressReg, .const offset]) with
  | none =>
    simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address] using Below.refl source.memory
  | some target =>
    cases stored : memStoreByteAuxExact source.memory source.mdomain source.be target 0#8 with
    | none =>
      simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address, getVar, zeroReg, stored] using
        Below.refl source.memory
    | some memory =>
      simpa [evaluate_inst, StackSemInst.instHOL, instInteger, address, getVar, zeroReg, stored] using
        byteStore source.memory memory source.mdomain source.be target stored

/-- Match an actual literal-zero assignment followed by a word store and the
remaining program; no assumption about address or domain validity is needed. -/
theorem Clears.wordStoreThen {C F : Type} (reg addressReg : Nat) (offset : BitVec 64)
    (rest : HolProg 64) (restClears : Clears (C := C) (F := F) rest) :
    Clears (C := C) (F := F) (.seq (.inst (.const reg 0#64))
      (.seq (.inst (.mem .store reg (.addr addressReg offset))) rest)) := by
  intro source
  rw [seqEvaluate]
  simp only [evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp, Option.join_some]
  exact seqAt _ rest (setVar reg (.word 0#64) source)
    (wordStoreZero _ reg addressReg offset (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])) restClears

theorem Clears.byteStoreThen {C F : Type} (reg addressReg : Nat) (offset : BitVec 64)
    (rest : HolProg 64) (restClears : Clears (C := C) (F := F) rest) :
    Clears (C := C) (F := F) (.seq (.inst (.const reg 0#64))
      (.seq (.inst (.mem .store8 reg (.addr addressReg offset))) rest)) := by
  intro source
  rw [seqEvaluate]
  simp only [evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp, Option.join_some]
  exact seqAt _ rest (setVar reg (.word 0#64) source)
    (byteStoreZero _ reg addressReg offset (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])) restClears

end InitECandidate.Solver.GuestWork.ZeroMemory
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.wordStoreZero
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.byteStoreZero
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.wordStoreThen
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Clears.byteStoreThen
