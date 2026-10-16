import InitECandidate.Solver.GuestWork.FrameAllocBounded
import InitECandidate.Solver.FlattenWeighted.BlockBound

namespace InitECandidate.Solver.GuestWork.FrameAllocEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option linter.unusedSimpArgs false
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

/-- Actual allocator Work bound under its valid-call guards, for every initial clock. -/
theorem work_all_clocks {C F : Type}
    (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (hheap : source.regs.lookup 26 = some (.word heap))
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hamount : source.regs.lookup 10 = some (.word amount))
    (hreturn : source.regs.lookup 1 = some (.loc returnLabel returnOffset))
    (stackSafe : ¬ stack - 32#64 < metadata)
    (metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true)
    (metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset)
    (globalsEq : (offset <<< (1 : Nat)) + heap = globals)
    (pointerDomain : source.mdomain (globals + 18446744073709551584#64) = true)
    (pointerValue : source.memory (globals + 18446744073709551584#64) = .word pointer)
    (scratchDomain : source.mdomain (globals + 18446744073709551592#64) = true)
    (scratchValue : source.memory (globals + 18446744073709551592#64) = .word scratch)
    (saveDomain : source.mdomain (stack - 32#64 + 24#64) = true)
    (metadataNotSave : metadata + 18446744073709551592#64 ≠ stack - 32#64 + 24#64)
    (scratchNotSave : globals + 18446744073709551592#64 ≠ stack - 32#64 + 24#64)
    (fits : ¬ scratch - pointer < amount)
    (roundedFits : ¬ scratch < ((amount + pointer + 7#64) &&& 18446744073709551608#64))
 : Work Named71.2 source 58 := by
  have roundedGuard : ¬ scratch < AndOp.and (amount + pointer + 7#64) (18446744073709551608#64) := roundedFits
  have mask : AndOp.and (18446744073709551608#64) (18446744073709551615#64) = 18446744073709551608#64 := by decide
  by_cases enough : 4 ≤ source.clock
  · exact work source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset
      hmetadata hheap hstack hamount hreturn stackSafe metadataDomain metadataValue globalsEq pointerDomain pointerValue scratchDomain scratchValue saveDomain metadataNotSave scratchNotSave fits roundedFits enough
  · have options : source.clock = 0 ∨ source.clock = 1 ∨ source.clock = 2 ∨ source.clock = 3 := by omega
    rcases options with clock | clock | clock | clock
    all_goals
      refine Work.seq (firstCredit := 7) (secondCredit := 51) ?_ ?_
      ·
        exact Work.basic (by decide)
      · intro state1 run1
        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
          fits, mask, roundedGuard, clock,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run1
        all_goals
          subst state1
          refine Work.seq (firstCredit := 1) (secondCredit := 50) ?_ ?_
          ·
            exact Work.basic (by decide)
          · intro state2 run2
            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
              fits, mask, roundedGuard, clock,
              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run2
            all_goals
              subst state2
              refine Work.seq (firstCredit := 1) (secondCredit := 49) ?_ ?_
              ·
                exact Work.basic (by decide)
              · intro state3 run3
                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                  fits, mask, roundedGuard, clock,
                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run3
                all_goals
                  subst state3
                  refine Work.seq (firstCredit := 1) (secondCredit := 48) ?_ ?_
                  ·
                    exact Work.basic (by decide)
                  · intro state4 run4
                    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                      seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                      wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                      hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                      metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                      scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                      fits, mask, roundedGuard, clock,
                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run4
                    all_goals
                      subst state4
                      refine Work.seq (firstCredit := 1) (secondCredit := 47) ?_ ?_
                      ·
                        exact Work.basic (by decide)
                      · intro state5 run5
                        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                          fits, mask, roundedGuard, clock,
                          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run5
                        all_goals
                          subst state5
                          refine Work.seq (firstCredit := 1) (secondCredit := 46) ?_ ?_
                          ·
                            exact Work.basic (by decide)
                          · intro state6 run6
                            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                              fits, mask, roundedGuard, clock,
                              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run6
                            all_goals
                              subst state6
                              refine Work.seq (firstCredit := 1) (secondCredit := 45) ?_ ?_
                              ·
                                exact Work.basic (by decide)
                              · intro state7 run7
                                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                  fits, mask, roundedGuard, clock,
                                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run7
                                all_goals
                                  subst state7
                                  refine Work.seq (firstCredit := 1) (secondCredit := 44) ?_ ?_
                                  ·
                                    exact Work.basic (by decide)
                                  · intro state8 run8
                                    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                      seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                      wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                      hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                      metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                      scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                      fits, mask, roundedGuard, clock,
                                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run8
                                    all_goals
                                      subst state8
                                      refine Work.seq (firstCredit := 1) (secondCredit := 43) ?_ ?_
                                      ·
                                        exact Work.basic (by decide)
                                      · intro state9 run9
                                        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                          fits, mask, roundedGuard, clock,
                                          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run9
                                        all_goals
                                          subst state9
                                          refine Work.seq (firstCredit := 1) (secondCredit := 42) ?_ ?_
                                          ·
                                            exact Work.basic (by decide)
                                          · intro state10 run10
                                            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                              fits, mask, roundedGuard, clock,
                                              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run10
                                            all_goals
                                              subst state10
                                              refine Work.seq (firstCredit := 1) (secondCredit := 41) ?_ ?_
                                              ·
                                                exact Work.basic (by decide)
                                              · intro state11 run11
                                                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                  fits, mask, roundedGuard, clock,
                                                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run11
                                                all_goals
                                                  subst state11
                                                  refine Work.seq (firstCredit := 5) (secondCredit := 36) ?_ ?_
                                                  ·
                                                    apply Work.ite (credits := 4)
                                                    · intro chosen
                                                      simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,
                                                        HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, mask,
                                                        fits, roundedGuard, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at chosen
                                                    · intro _
                                                      exact Work.basic (by decide)
                                                  · intro state12 run12
                                                    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                      seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                      wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                      hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                      metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                      scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                      fits, mask, roundedGuard, clock,
                                                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run12
                                                    all_goals
                                                      subst state12
                                                      refine Work.seq (firstCredit := 2) (secondCredit := 34) ?_ ?_
                                                      ·
                                                        exact Work.basic (by decide)
                                                      · intro state13 run13
                                                        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                          fits, mask, roundedGuard, clock,
                                                          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run13
                                                        all_goals
                                                          subst state13
                                                          refine Work.seq (firstCredit := 1) (secondCredit := 33) ?_ ?_
                                                          ·
                                                            exact Work.basic (by decide)
                                                          · intro state14 run14
                                                            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                              fits, mask, roundedGuard, clock,
                                                              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run14
                                                            all_goals
                                                              subst state14
                                                              refine Work.seq (firstCredit := 1) (secondCredit := 32) ?_ ?_
                                                              ·
                                                                exact Work.basic (by decide)
                                                              · intro state15 run15
                                                                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                  fits, mask, roundedGuard, clock,
                                                                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run15
                                                                all_goals
                                                                  subst state15
                                                                  refine Work.seq (firstCredit := 1) (secondCredit := 31) ?_ ?_
                                                                  ·
                                                                    exact Work.basic (by decide)
                                                                  · intro state16 run16
                                                                    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                      seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                      wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                      hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                      metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                      scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                      fits, mask, roundedGuard, clock,
                                                                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run16
                                                                    all_goals
                                                                      subst state16
                                                                      refine Work.seq (firstCredit := 1) (secondCredit := 30) ?_ ?_
                                                                      ·
                                                                        exact Work.basic (by decide)
                                                                      · intro state17 run17
                                                                        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                          fits, mask, roundedGuard, clock,
                                                                          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run17
                                                                        all_goals
                                                                          subst state17
                                                                          refine Work.seq (firstCredit := 1) (secondCredit := 29) ?_ ?_
                                                                          ·
                                                                            exact Work.basic (by decide)
                                                                          · intro state18 run18
                                                                            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                              fits, mask, roundedGuard, clock,
                                                                              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run18
                                                                            all_goals
                                                                              subst state18
                                                                              refine Work.seq (firstCredit := 1) (secondCredit := 28) ?_ ?_
                                                                              ·
                                                                                exact Work.basic (by decide)
                                                                              · intro state19 run19
                                                                                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                                  fits, mask, roundedGuard, clock,
                                                                                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run19
                                                                                all_goals
                                                                                  subst state19
                                                                                  refine Work.seq (firstCredit := 1) (secondCredit := 27) ?_ ?_
                                                                                  ·
                                                                                    exact Work.basic (by decide)
                                                                                  · intro state20 run20
                                                                                    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                                      seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                                      wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                                      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                                      hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                                      metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                                      scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                                      fits, mask, roundedGuard, clock,
                                                                                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run20
                                                                                    all_goals
                                                                                      subst state20
                                                                                      refine Work.seq (firstCredit := 1) (secondCredit := 26) ?_ ?_
                                                                                      ·
                                                                                        exact Work.basic (by decide)
                                                                                      · intro state21 run21
                                                                                        simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                                          seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                                          wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                                          assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                                          hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                                          metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                                          scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                                          fits, mask, roundedGuard, clock,
                                                                                          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run21
                                                                                        all_goals
                                                                                          subst state21
                                                                                          refine Work.seq (firstCredit := 1) (secondCredit := 25) ?_ ?_
                                                                                          ·
                                                                                            exact Work.basic (by decide)
                                                                                          · intro state22 run22
                                                                                            simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                                              seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                                              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                                              wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                                              assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                                              hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                                              metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                                              scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                                              fits, mask, roundedGuard, clock,
                                                                                              HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run22
                                                                                            all_goals
                                                                                              subst state22
                                                                                              refine Work.seq (firstCredit := 5) (secondCredit := 20) ?_ ?_
                                                                                              ·
                                                                                                apply Work.ite (credits := 4)
                                                                                                · intro chosen
                                                                                                  simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,
                                                                                                    HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, mask,
                                                                                                    fits, roundedGuard, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at chosen
                                                                                                · intro _
                                                                                                  exact Work.basic (by decide)
                                                                                              · intro state23 run23
                                                                                                simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
                                                                                                  seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
                                                                                                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                                                                                                  wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
                                                                                                  assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
                                                                                                  hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
                                                                                                  metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
                                                                                                  scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
                                                                                                  fits, mask, roundedGuard, clock,
                                                                                                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run23
                                                                                                all_goals
                                                                                                  subst state23
                                                                                                  exact Work.basic (by decide)

/-- Every insufficient-clock allocator run times out with no remaining clock. -/
theorem small_timeout {C F : Type}
    (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (valid : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (smallClock : source.clock < 4) :
    (evaluate (Named71.2, source)).1 = some .timeOut ∧
    (evaluate (Named71.2, source)).2.clock = 0 := by
  obtain ⟨hmetadata, hheap, hstack, hamount, hreturn, stackSafe, metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue, scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave, fits, roundedFits⟩ := valid
  have roundedGuard : ¬ scratch < AndOp.and (amount + pointer + 7#64) (18446744073709551608#64) := roundedFits
  have mask : AndOp.and (18446744073709551608#64) (18446744073709551615#64) = 18446744073709551608#64 := by decide
  have options : source.clock = 0 ∨ source.clock = 1 ∨ source.clock = 2 ∨ source.clock = 3 := by omega
  rcases options with clock | clock | clock | clock
  all_goals
    simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
    seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
    wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
    assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
    hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
    metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
    scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
    fits, mask, roundedGuard, clock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, emptyEnv]

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.work_all_clocks
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.small_timeout
