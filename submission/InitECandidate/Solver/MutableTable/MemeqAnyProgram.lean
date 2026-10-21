import InitECandidate.Solver.MutableTable.MemeqAnyModel
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Program

set_option maxRecDepth 100000

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def guard52 : ProgHOL 64 := match Memeq32.parts.otherAligned with | .seq guard _=>guard | _=>.skip
def after52 : ProgHOL 64 := match Memeq32.parts.otherAligned with | .seq _ rest=>rest | _=>.skip
def word32Body : ProgHOL 64 := match after52 with | .seq (.while _ body) _=>body | _=>.skip
def word8Body : ProgHOL 64 := match after52 with | .seq _ (.while _ body)=>body | _=>.skip
def blockTest (stride : Nat) : ExpHOL 64 := .cmp .notLower (localVar "n") (.op .add [localVar "i",.const (BitVec.ofNat 64 stride)])

theorem other_shape : Memeq32.parts.otherAligned=.seq guard52 (.seq (.while (blockTest 32) word32Body) (.while (blockTest 8) word8Body)) := by
  simp only [guard52,after52,word32Body,word8Body,blockTest,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,localVar,List.map_cons,List.map_nil]

theorem decisions : Input.PureDecision Memeq32.parts.twenty ∧ Input.PureDecision Memeq32.parts.thirtyTwo ∧ Input.PureDecision guard52 := by
  constructor
  · simp only [Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
    repeat first | apply Input.PureDecision.seq | apply Input.PureDecision.ite | exact Input.PureDecision.returned _ | exact Input.PureDecision.skip
  · constructor
    · simp only [Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
      repeat first | apply Input.PureDecision.seq | apply Input.PureDecision.ite | exact Input.PureDecision.returned _ | exact Input.PureDecision.skip
    · simp only [guard52,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
      repeat first | apply Input.PureDecision.seq | apply Input.PureDecision.ite | exact Input.PureDecision.returned _ | exact Input.PureDecision.skip

/-- Literal original counter bodies, with arbitrary comparison reads. -/
theorem guarded_bodies : Input.GuardedCounter 32 word32Body ∧ Input.GuardedCounter 8 word8Body ∧
    Input.GuardedCounter 8 MemeqByteRuntime.blockBody ∧ Input.GuardedCounter 1 MemeqByteRuntime.byteBody := by
  constructor
  · simp only [word32Body,after52,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
    repeat first | apply Input.GuardedCounter.checks | exact Input.PureDecision.ite _ (.returned _) .skip | exact Input.GuardedCounter.increment
  · constructor
    · simp only [word8Body,after52,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
      repeat first | apply Input.GuardedCounter.checks | exact Input.PureDecision.ite _ (.returned _) .skip | exact Input.GuardedCounter.increment
    · constructor
      · simp only [MemeqByteRuntime.blockBody,Memeq32.byteBodies,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
        repeat first | apply Input.GuardedCounter.checks | exact Input.PureDecision.ite _ (.returned _) .skip | exact Input.GuardedCounter.increment
      · simp only [MemeqByteRuntime.byteBody,Memeq32.byteBodies,Memeq32.parts,Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
        repeat first | apply Input.GuardedCounter.checks | exact Input.PureDecision.ite _ (.returned _) .skip | exact Input.GuardedCounter.increment

theorem block_test_reads (stride : Nat) (strideBound : stride≤32) : Input.GuardedCounterLoop.TestReads (blockTest stride) stride 32 := by
  intro source word cell nCell bounded
  have small : stride<2^64 := by omega
  have number : (word+BitVec.ofNat 64 stride).toNat=word.toNat+stride := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have compare : ((32#64 : BitVec 64)<word+BitVec.ofNat 64 stride)↔32<word.toNat+stride := by
    change 32<(word+BitVec.ofNat 64 stride).toNat↔_
    rw [number]
  by_cases active : word.toNat+stride≤32
  · have below : ¬32<word.toNat+stride := by omega
    simp [blockTest,evalHOLFinite,evalHOLExact,evalListHOLExact,localVar,toExact,cell,nCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,below]
  · have above : 32<word.toNat+stride := by omega
    simp [blockTest,evalHOLFinite,evalHOLExact,evalListHOLExact,localVar,toExact,cell,nCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,above]

theorem byte_test_reads : Input.GuardedCounterLoop.TestReads Memeq32.condition1 1 32 := by
  intro source word cell nCell bounded
  have compare : ((word : BitVec 64)<32#64)↔word.toNat<32 := Iff.rfl
  by_cases active : word.toNat+1≤32
  · have below : word.toNat<32 := by omega
    simp [Memeq32.condition1,evalHOLFinite,evalHOLExact,localVar,toExact,cell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,below]
  · have above : ¬word.toNat<32 := by omega
    simp [Memeq32.condition1,evalHOLFinite,evalHOLExact,localVar,toExact,cell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,above]

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.other_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.decisions
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.guarded_bodies
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.block_test_reads
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.byte_test_reads
