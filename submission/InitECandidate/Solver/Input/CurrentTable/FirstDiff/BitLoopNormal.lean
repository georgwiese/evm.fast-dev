import InitECandidate.Solver.Input.CurrentTable.FirstDiff.BitFacts
import InitECandidate.Solver.Input.LoopControlExit
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.WitnessRadix.BindingLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open WitnessRadix.QueryBranch

theorem bit_limit_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (position : Nat) (bounded : position ≤ 8)
    (cell : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position)))) :
    evalHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) bitLimit =
      some (.val (.word (if position < 8 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 position).toNat = position := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have small : position < 9223372036854775808 := by omega
  simp [bitLimit,localVar,evalHOLFinite,evalHOLExact,cell,wordCmpHOL,holAsmSignedLess,number,small]

/-- A genuinely continuing bit step skipped its return, so that digit was
zero. The actual j increment and x preservation are retained. -/
theorem bit_step_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (word : BitVec 64) (position : Nat) (inside : position < 8)
    (wordCell : source.locals.lookup (ofString "x") = some (.val (.word word)))
    (counterCell : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position))))
    (normal : evaluateHOLFiniteState source bitStep = (none,post)) :
    word.getLsbD (7-position) = false ∧
      post.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 (position+1)))) ∧
      post.locals.lookup (ofString "x") = some (.val (.word word)) := by
  have stepRun := normal
  rw [shapes.2.2.2.2.2.2.2.2.1] at stepRun
  obtain ⟨middle,guardRun,incrementRun⟩ := Input.sequence_none source post _ _ stepRun
  have read := bit_test_read source word position inside wordCell counterCell
  have clear : word.getLsbD (7-position) = false := by
    cases digit : word.getLsbD (7-position) with
    | false => rfl
    | true =>
      rw [digit] at read
      rw [shapes.2.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite] at guardRun
      simp only [eval] at read
      rw [read] at guardRun
      simp only [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)] at guardRun
      exact ((NoFallthrough.returned bitResult) source (congrArg Prod.fst guardRun)).elim
  have next := bit_advance source post (BitVec.ofNat 64 position) counterCell normal
  have xSaved := (bit_flow (ofString "x") (by decide)).none_preserves source post normal
  refine ⟨clear,?_,xSaved.trans wordCell⟩
  simpa only [BitVec.ofNat_add] using next

def BitInvariant (byte : BitVec 8) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ position : Nat,position ≤ 8 ∧
    source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position))) ∧
    source.locals.lookup (ofString "x") = some (.val (.word (byte.setWidth 64))) ∧
    ∀ prior,prior < position → byte.getLsbD (7-prior) = false

/-- The inner loop can fall through only after all eight actual byte digits
were zero. A nonzero xor therefore returns or stops; it cannot advance i. -/
theorem bit_loop_none_zero (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8) (ready : BitInvariant byte source)
    (normal : evaluateHOLFiniteState source bitLoop = (none,post)) : byte = 0#8 := by
  rw [shapes.2.2.2.2.2.2.2.1] at normal
  apply loop_control_exit bitLimit bitStep (BitInvariant byte) (fun _ => byte = 0#8) _ _ _ source post ready normal
  · intro current valid stopped
    obtain ⟨position,bounded,counterCell,wordCell,before⟩ := valid
    have read := bit_limit_read current position bounded counterCell
    have full : position = 8 := by
      by_cases active : position < 8
      · rw [if_pos active] at read
        have impossible := stopped.symm.trans read
        cases impossible
      · omega
    apply BitVec.eq_of_getLsbD_eq
    intro digit inside
    have reverse : 7-(7-digit) = digit := by omega
    have absent := before (7-digit) (by omega)
    simpa only [reverse,BitVec.getLsbD_zero] using absent
  · intro current valid observed actual nonzero funded target result run continuing
    obtain ⟨position,bounded,counterCell,wordCell,before⟩ := valid
    have read := bit_limit_read current position bounded counterCell
    have active : position < 8 := by
      by_contra inactive
      rw [if_neg inactive] at read
      have same : observed = 0#64 := by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero same
    have controls := (bit_flow (ofString "x") (by decide)).summary (decClockHOLFinite current)
    have normalResult : result = none := by
      rcases continuing with fallthrough | continued
      · exact fallthrough
      · have impossible := controls.2.2
        rw [run] at impossible
        exact (impossible continued).elim
    subst result
    obtain ⟨clear,next,saved⟩ := bit_step_none (decClockHOLFinite current) target (byte.setWidth 64)
      position active wordCell counterCell run
    have clearByte : byte.getLsbD (7-position) = false := by
      simpa only [BitVec.getLsbD_setWidth,show decide (7-position < 64) = true from by simp; omega,Bool.true_and] using clear
    refine ⟨position+1,by omega,next,saved,?_⟩
    intro prior earlier
    by_cases old : prior < position
    · exact before prior old
    · have same : prior = position := by omega
      simpa only [same] using clearByte
  · intro current valid observed actual nonzero funded target run
    have controls := (bit_flow (ofString "x") (by decide)).summary (decClockHOLFinite current)
    have impossible := controls.2.1
    rw [run] at impossible
    exact (impossible rfl).elim

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_limit_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_step_none
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_loop_none_zero
