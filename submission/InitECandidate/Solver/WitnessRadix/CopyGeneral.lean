import InitECandidate.Solver.WitnessRadix.CopyGeneralState
import InitECandidate.Solver.WitnessRadix.Copy32Tests

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch CopyContext

def aligned (src dst : BitVec 64) : Prop := (dst ||| src) &&& 7#64 = 0#64
instance (src dst : BitVec 64) : Decidable (aligned src dst) := inferInstanceAs (Decidable (_ = _))
def cost (src dst : BitVec 64) (length : Nat) : Nat :=
  if aligned src dst then CopyWords.prefixCost length + CopyBytes.suffixCost (CopyWords.prefixIndex length) length
  else CopyBytes.suffixCost 0 length
def coreState {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) : PanSemStateFiniteExact 64 F :=
  if aligned src dst then CopyBytes.suffixState (CopyWords.prefixState source src dst length) src dst (CopyWords.prefixIndex length) length
  else CopyBytes.suffixState source src dst 0 length

theorem cost_le (src dst : BitVec 64) (length : Nat) : cost src dst length ≤ length := by
  unfold cost
  split
  · have bounds := CopyWords.prefix_bounds length
    have suffix := suffix_cost_le (CopyWords.prefixIndex length) length
    omega
  · have suffix := suffix_cost_le 0 length
    omega

theorem core_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    (coreState source src dst length).clock = source.clock - cost src dst length := by
  unfold coreState cost
  split <;> simp only [CopyBytes.suffix_clock, CopyWords.prefix_clock] <;> omega

theorem core_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    control (coreState source src dst length) = control source := by
  unfold coreState
  split <;> simp only [suffix_control, prefix_control]

theorem alignment_false {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (args : Args source src dst length) (mask : ¬ aligned src dst) :
    eval source Copy32.alignment = some (.val (.word 0#64)) := by
  have opOr : wordOpHOL .or [dst, src] = some (dst ||| src) := by
    change some (dst ||| (src ||| 0#64)) = _
    rw [BitVec.or_zero]
  have opAnd : wordOpHOL .and [dst ||| src, 7#64] = some ((dst ||| src) &&& 7#64) := by
    change some ((dst ||| src) &&& (7#64 &&& ~~~(0#64))) = _
    rw [BitVec.not_zero, BitVec.and_allOnes]
  unfold aligned at mask
  simp only [eval, Copy32.alignment, localVar, evalHOLExact, evalListHOLExact, toExact, args.srcLocal, args.dstLocal,
    valueIsWord, valueWord, List.all_cons, List.all_nil, Bool.and_self, List.map_cons, List.map_nil,
    opOr, opAnd, Option.map_some, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp [mask]

theorem core_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (args : Args source src dst length) (mapped : Mapped source src dst length)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (small : length + 32 < 2 ^ 64) (enough : cost src dst length ≤ source.clock) :
    evaluateHOLFiniteState source (.seq (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)
      (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64))))) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (coreState source src dst length)) := by
  classical
  by_cases mask : aligned src dst
  · have costEq : cost src dst length = CopyWords.prefixCost length + CopyBytes.suffixCost (CopyWords.prefixIndex length) length := if_pos mask
    have prefixRun := CopyWords.prefix_execute source src dst length args mapped indexLocal mask small (by rw [costEq] at enough; omega)
    have read := Copy32.alignment_read source src dst args.srcLocal args.dstLocal mask
    simp only [eval] at read
    have chosen : evaluateHOLFiniteState source (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip) =
        (none, CopyWords.prefixState source src dst length) := by
      rw [evaluateHOLFiniteState_ite, read]
      simpa using prefixRun
    have prefixArgs := prefix_args source src dst length args
    have prefixMapped := Mapped.of_domain source (CopyWords.prefixState source src dst length) src dst length (prefix_domain source src dst length) mapped
    have suffix := CopyBytes.suffix_execute (CopyWords.prefixState source src dst length) src dst (CopyWords.prefixIndex length) length
      prefixArgs prefixMapped (CopyWords.prefix_index source src dst length indexLocal)
      (CopyWords.prefix_bounds length).1 small (by rw [CopyWords.prefix_clock]; rw [costEq] at enough; omega)
    rw [StateSteps.next_sequence source (CopyWords.prefixState source src dst length) _ _ chosen (by rw [CopyWords.prefix_clock]; omega)]
    simpa only [coreState, if_pos mask] using suffix
  · have read := alignment_false source src dst length args mask
    simp only [eval] at read
    have chosen : evaluateHOLFiniteState source (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip) = (none, source) := by
      rw [evaluateHOLFiniteState_ite, read]
      simp [evaluateHOLFiniteState_skip]
    rw [StateSteps.next_sequence source source _ _ chosen (Nat.le_refl _)]
    have suffix := CopyBytes.suffix_execute source src dst 0 length args mapped indexLocal (Nat.zero_le _) small
      (by simpa only [cost, if_neg mask] using enough)
    simpa only [coreState, if_neg mask] using suffix

/-- The complete fixed memcpy, including all four loops, arbitrary alignment,
lexical scopes and return. Its source-clock cost is at most its byte length. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (args : Args source src dst length) (mapped : Mapped source src dst length)
    (small : length + 32 < 2 ^ 64) (enough : cost src dst length ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source Copy32.body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with
        memory := (coreState (bind source "i" 0#64) src dst length).memory, clock := source.clock - cost src dst length } := by
  classical
  let initial := bind source "i" 0#64
  have initialArgs : Args initial src dst length := by
    constructor
    · exact (bind_lookup_other source "i" "src" _ (by decide)).trans args.srcLocal
    · exact (bind_lookup_other source "i" "dst" _ (by decide)).trans args.dstLocal
    · exact (bind_lookup_other source "i" "n" _ (by decide)).trans args.lengthLocal
  have initialMapped := Mapped.of_domain source initial src dst length rfl mapped
  have core := core_execute initial src dst length initialArgs initialMapped (bind_lookup_same _ _ _) small enough
  let target := restore source "i" (emptyLocalsHOLFinite (coreState initial src dst length))
  refine ⟨target, ?_, ?_⟩
  · rw [Copy32.body_shape, evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
    change (let output := (evaluateHOLFiniteState initial
        (.seq (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)
          (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64))))))
      (output.1, restore source "i" output.2)) = _
    rw [core]
  · have frame := frame_of_control initial (coreState initial src dst length) (core_control initial src dst length)
    have clock := core_clock initial src dst length
    change emptyLocalsHOLFinite (coreState initial src dst length) = _
    rw [frame, clock]
    rfl

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.cost_le
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.core_clock
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.core_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.alignment_false
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.core_execute
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.execute
