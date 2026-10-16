import InitECandidate.Solver.FlattenWeighted.LoopClockRank
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroBytes
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual unaligned eight-byte loop of fixed Named78 (memzero). -/
def body : HolProg 64 := NamedBody78_202

theorem body_basic : basic body = true := by decide
theorem body_nodes : nodes body = 83 := by decide
theorem body_ticks : ticks body = 2 := by decide

theorem body_work {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    Work body source 85 := by
  have h := Work.basic (source := source) body_basic
  simpa only [body_ticks, body_nodes] using h

theorem body_clock {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    source.clock ≤ (evaluate (body, source)).2.clock + 2 := by
  simpa only [body_ticks] using basicClock body source body_basic

private theorem evaluateSeq {C F : Type} (p q : HolProg 64)
    (s : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, s) =
      match evaluate (p, s) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, s) with ⟨result, next⟩
  cases result <;> rfl

/-- Successful continuation and normal loop exit expose the actual guard and
register updates. Failed stores and timeouts satisfy neither premise. -/
theorem body_outcome {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (execution : evaluate (body, source) = (result, post)) :
    (StackSemControl.contLoop result = true →
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word (index + 8#64)) ∧ index + 8#64 ≤ length) ∧
    (result = some (.break 0) →
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word index) ∧ length < index + 8#64) := by
  by_cases less : length < index + 8#64
  · by_cases zero : source.clock = 0
    all_goals
      simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
            evaluate_inst, evaluate_continue, evaluate_break,
            StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
            hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
            StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
            setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
      rcases execution with ⟨rfl, rfl⟩
      simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · by_cases zero : source.clock = 0
    ·
      simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
            evaluate_inst, evaluate_continue, evaluate_break,
            StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
            hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
            StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
            setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
      rcases execution with ⟨rfl, rfl⟩
      simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    ·
      cases store0 : memStoreByteAuxExact source.memory source.mdomain source.be (index + base) 0#8 with
      | none =>
        simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
              evaluate_inst, evaluate_continue, evaluate_break,
              StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
              hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
              StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
              setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0] at execution
        rcases execution with ⟨rfl, rfl⟩
        simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      | some memory0 =>
        cases store1 : memStoreByteAuxExact memory0 source.mdomain source.be (index + base + 1#64) 0#8 with
        | none =>
          simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                evaluate_inst, evaluate_continue, evaluate_break,
                StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1] at execution
          rcases execution with ⟨rfl, rfl⟩
          simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        | some memory1 =>
          cases store2 : memStoreByteAuxExact memory1 source.mdomain source.be (index + base + 2#64) 0#8 with
          | none =>
            simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                  evaluate_inst, evaluate_continue, evaluate_break,
                  StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                  hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                  StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                  setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2] at execution
            rcases execution with ⟨rfl, rfl⟩
            simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          | some memory2 =>
            cases store3 : memStoreByteAuxExact memory2 source.mdomain source.be (index + base + 3#64) 0#8 with
            | none =>
              simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                    evaluate_inst, evaluate_continue, evaluate_break,
                    StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                    hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                    StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                    setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3] at execution
              rcases execution with ⟨rfl, rfl⟩
              simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
            | some memory3 =>
              cases store4 : memStoreByteAuxExact memory3 source.mdomain source.be (index + base + 4#64) 0#8 with
              | none =>
                simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                      evaluate_inst, evaluate_continue, evaluate_break,
                      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                      hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                      setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3, store4] at execution
                rcases execution with ⟨rfl, rfl⟩
                simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
              | some memory4 =>
                cases store5 : memStoreByteAuxExact memory4 source.mdomain source.be (index + base + 5#64) 0#8 with
                | none =>
                  simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                        evaluate_inst, evaluate_continue, evaluate_break,
                        StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                        hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                        StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                        setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3, store4, store5] at execution
                  rcases execution with ⟨rfl, rfl⟩
                  simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
                | some memory5 =>
                  cases store6 : memStoreByteAuxExact memory5 source.mdomain source.be (index + base + 6#64) 0#8 with
                  | none =>
                    simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                          evaluate_inst, evaluate_continue, evaluate_break,
                          StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                          hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                          StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                          setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3, store4, store5, store6] at execution
                    rcases execution with ⟨rfl, rfl⟩
                    simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
                  | some memory6 =>
                    cases store7 : memStoreByteAuxExact memory6 source.mdomain source.be (index + base + 7#64) 0#8 with
                    | none =>
                      simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                            evaluate_inst, evaluate_continue, evaluate_break,
                            StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                            hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                            StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                            setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3, store4, store5, store6, store7] at execution
                      rcases execution with ⟨rfl, rfl⟩
                      simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
                    | some memory7 =>
                      simp [body, NamedBody78_120, NamedBody78_121, NamedBody78_122, NamedBody78_123, NamedBody78_124, NamedBody78_125, NamedBody78_126, NamedBody78_127, NamedBody78_128, NamedBody78_129, NamedBody78_130, NamedBody78_131, NamedBody78_132, NamedBody78_133, NamedBody78_134, NamedBody78_135, NamedBody78_136, NamedBody78_137, NamedBody78_138, NamedBody78_139, NamedBody78_140, NamedBody78_141, NamedBody78_142, NamedBody78_143, NamedBody78_144, NamedBody78_145, NamedBody78_146, NamedBody78_147, NamedBody78_148, NamedBody78_149, NamedBody78_150, NamedBody78_151, NamedBody78_152, NamedBody78_153, NamedBody78_154, NamedBody78_155, NamedBody78_156, NamedBody78_157, NamedBody78_158, NamedBody78_159, NamedBody78_160, NamedBody78_161, NamedBody78_162, NamedBody78_163, NamedBody78_164, NamedBody78_165, NamedBody78_166, NamedBody78_167, NamedBody78_168, NamedBody78_169, NamedBody78_170, NamedBody78_171, NamedBody78_172, NamedBody78_173, NamedBody78_174, NamedBody78_175, NamedBody78_176, NamedBody78_177, NamedBody78_178, NamedBody78_179, NamedBody78_180, NamedBody78_181, NamedBody78_182, NamedBody78_183, NamedBody78_184, NamedBody78_185, NamedBody78_186, NamedBody78_187, NamedBody78_188, NamedBody78_189, NamedBody78_190, NamedBody78_191, NamedBody78_192, NamedBody78_193, NamedBody78_194, NamedBody78_195, NamedBody78_196, NamedBody78_197, NamedBody78_198, NamedBody78_199, NamedBody78_200, NamedBody78_201, NamedBody78_202, evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
                            evaluate_inst, evaluate_continue, evaluate_break,
                            StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
                            hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
                            StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
                            setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, store0, store1, store2, store3, store4, store5, store6, store7] at execution
                      rcases execution with ⟨rfl, rfl⟩
                      simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end InitECandidate.Solver.GuestWork.MemzeroBytes
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_basic
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_nodes
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_ticks
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_clock
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_outcome
