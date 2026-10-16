import InitECandidate.Solver.CrepToLoopBound.Assembly
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRelEvaluateCallCorrect

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem simplifyEntry {width : Nat} [NeZero width] (start : MlString) :
    crepSimpProgHOL (.call none start [] : CrepProgHOL width) = .call none start [] := by
  conv => lhs; unfold crepSimpProgHOL
  rfl

private theorem compileEntryShape {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (start : MlString) :
    compileHOLExact (width := width) context .ln (.call none start []) =
      .seq (.call none (some (findLabExact context start)) [] none) .skip := by
  simp [compileHOLExact, compileExpsHOLExact, genTemps, loopNestedSeqHOL]

/-- Quantitative entry simulation for the actual arithmetic-simplifying
whole-program compiler. The fixed-code ceiling remains an explicit premise. -/
theorem compiledEntry {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (source sourceFinal : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (label : Nat) (architecture : Compiler.Encoders.Asm.AsmArchitecture)
    (body : CrepProgHOL width) (result : Option (CrepResultHOLExact width))
    (safe : CodeSafe limit (crepSimpMapcsHOL source).code)
    (run : evalCrepSemHOLProgExact source (.call none start []) = (result, sourceFinal))
    (notError : result ≠ some .error)
    (state : crepToLoopStateRelExact source target)
    (memory : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (distinct : (programs.map Prod.fst).Nodup)
    (sourceCode : source.code = alistToFmapCodeExact programs)
    (targetCode : target.code = sptFromAList (compileProgHOLExact architecture programs))
    (empty : source.locals = HolFiniteMapExact.empty)
    (entry : holAlookup programs start = some ([], body))
    (entryLabel : (crepToLoopMakeFuncsExactHOL programs).lookup start = some (label, 0)) :
    ∃ (clock : Nat) (targetResult : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width F),
      clock ≤ (2 * limit + 4) * source.clock ∧
      LoopSemStateFiniteExact.evaluate (.call none (some label) [] none)
        { target with clock := clock } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      targetResult = resultToLoop result ∧ sourceFinal.ffi = targetFinal.ffi := by
  let context : CrepToLoopContextExact :=
    mkCtxtExact architecture HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL programs) 0
  have code2 : crepToLoopCodeRel2Exact context source.code target.code := by
    rw [sourceCode, targetCode]
    exact mkCtxtCodeImpCodeRel2Exact architecture programs start body ⟨distinct, entry⟩
  have code : crepToLoopCodeRelExact context (crepSimpMapcsHOL source).code target.code := code2
  have locals : crepToLoopLocalsRelExact context .ln (crepSimpMapcsHOL source).locals target.locals := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y n m hx
      simp [context, mkCtxtExact, HolFiniteMapExact.empty] at hx
    · intro v m hv
      simp [context, mkCtxtExact, HolFiniteMapExact.empty] at hv
    · intro n hn
      simp [sptMem, sptDomain, sptLookup] at hn
    · intro name value found
      change source.locals.lookup name = some value at found
      rw [empty] at found
      simp [HolFiniteMapExact.empty] at found
  have simplified := crepArithSimpProgCorrect (.call none start []) source result sourceFinal run notError
  rw [simplifyEntry] at simplified
  obtain ⟨extra, targetResult, targetFinal, budget, targetRun, finalState, _, _, _, finalResult, _⟩ :=
    compileCorrect limit (.call none start []) (crepSimpMapcsHOL source) safe
      (by simp [ceiling, cost, expsCost]) result (crepSimpMapcsHOL sourceFinal)
      target context .ln simplified notError state memory globals code locals
  rw [compileEntryShape, LoopSemStateFiniteExact.evaluate_Seq_Skip] at targetRun
  have findLabel : findLabExact context start = label := by
    simp [findLabExact, context, mkCtxtExact, entryLabel]
  rw [findLabel] at targetRun
  have initialClock : source.clock = target.clock := state.2.2.1
  have bound : extra ≤ (2 * limit + 3) * (source.clock - sourceFinal.clock) := by
    simpa [cost, expsCost, crepSimpMapcsHOL] using budget
  have enlarged := Nat.mul_le_mul_left (2 * limit + 3) (Nat.sub_le source.clock sourceFinal.clock)
  refine ⟨target.clock + extra, targetResult, targetFinal, ?_, targetRun, finalState, finalResult, finalState.2.2.2.2.1⟩
  rw [show 2 * limit + 4 = (2 * limit + 3) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.compiledEntry
