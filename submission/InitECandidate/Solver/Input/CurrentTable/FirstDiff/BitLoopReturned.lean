import InitECandidate.Solver.Input.CurrentTable.FirstDiff.BitLoopNormal
import InitECandidate.Solver.Input.ReturnFactsLoop
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual scalar expression returned by a taken bit test. -/
theorem bit_result_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (index : BitVec 64) (position : Nat)
    (iCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (jCell : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source bitResult = some (.val (.word (index*8#64+BitVec.ofNat 64 position))) := by
  simp [bitResult,eval,evalHOLExact,evalListHOLExact,localVar,iCell,jCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

def BitAnswer (byte : BitVec 8) (index : BitVec 64) (value : ValueHOL 64) : Prop :=
  ∃ position : Nat,position < 8 ∧ value = .val (.word (index*8#64+BitVec.ofNat 64 position)) ∧
    byte.getLsbD (7-position) = true ∧ ∀ prior,prior < position → byte.getLsbD (7-prior) = false

/-- A real early return is exactly its current tested nonzero digit. -/
theorem bit_step_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8) (index : BitVec 64) (position : Nat) (inside : position < 8)
    (wordCell : source.locals.lookup (ofString "x") = some (.val (.word (byte.setWidth 64))))
    (iCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (jCell : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source bitStep = (some (.returned value),post)) :
    value = .val (.word (index*8#64+BitVec.ofNat 64 position)) ∧ byte.getLsbD (7-position) = true := by
  have read := bit_test_read source (byte.setWidth 64) position inside wordCell jCell
  have widened : (byte.setWidth 64).getLsbD (7-position) = byte.getLsbD (7-position) := by
    simp [BitVec.getLsbD_setWidth,show 7-position < 64 from by omega]
  rw [widened] at read
  rw [shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2,
    evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at read
  rw [read] at normal
  cases digit : byte.getLsbD (7-position) with
  | false =>
    simp only [digit,↓reduceIte,evaluateHOLFiniteState_skip] at normal
    have safe : LocalPrefix (ofString "x") (increment "j") := .assign _ _ (by decide)
    exact ((safe.summary_full source).2.1 value (congrArg Prod.fst normal)).elim
  | true =>
    simp only [digit,↓reduceIte] at normal
    have expression := bit_result_read source index position iCell jCell
    simp only [eval] at expression
    rw [evaluateHOLFiniteState_return,expression] at normal
    simp only [shapeOfHOLExact,sizeOfShapeWithContextHOL,
      if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide),if_pos (show (1:Nat) ≤ 32 from by decide)] at normal
    have same := congrArg Prod.fst normal
    have valueEq : .val (.word (index*8#64+BitVec.ofNat 64 position)) = value := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using same
    exact ⟨valueEq.symm,rfl⟩

/-- Actual loop returns select the least nonzero digit of the read byte. -/
theorem bit_loop_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8) (index : BitVec 64) (ready : BitInvariant byte source)
    (iCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source bitLoop = (some (.returned value),post)) :
    BitAnswer byte index value := by
  rw [shapes.2.2.2.2.2.2.2.1] at normal
  apply ReturnFacts.loop source.code bitLimit bitStep
    (fun current => BitInvariant byte current ∧ current.locals.lookup (ofString "i") = some (.val (.word index)))
    (BitAnswer byte index) _ _ source rfl ⟨ready,iCell⟩ post value normal
  · intro current installed valid observed actual nonzero funded target value run
    obtain ⟨⟨position,bounded,jCell,xCell,before⟩,savedI⟩ := valid
    have read := bit_limit_read current position bounded jCell
    have active : position < 8 := by
      by_contra inactive
      rw [if_neg inactive] at read
      have same : observed = 0#64 := by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
      exact nonzero same
    obtain ⟨answer,digit⟩ := bit_step_returned (decClockHOLFinite current) target byte index position
      active xCell savedI jCell value run
    exact ⟨position,active,answer,digit,before⟩
  · intro current installed valid observed actual nonzero funded target result run continuing
    have controls := (bit_flow (ofString "i") (by decide)).summary (decClockHOLFinite current)
    have normalResult : result = none := by
      rcases continuing with fallthrough | continued
      · exact fallthrough
      · have impossible := controls.2.2
        rw [run] at impossible
        exact (impossible continued).elim
    have normalRun : evaluateHOLFiniteState (decClockHOLFinite current) bitStep = (none,target) := by
      simpa only [normalResult] using run
    have saved := (bit_flow (ofString "i") (by decide)).none_preserves (decClockHOLFinite current) target normalRun
    exact ⟨bit_progress current byte valid.1 observed actual nonzero target result run continuing,saved.trans valid.2⟩

/-- The actual j declaration starts this same least-digit proof at zero. -/
theorem different_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8) (index : BitVec 64)
    (xCell : source.locals.lookup (ofString "x") = some (.val (.word (byte.setWidth 64))))
    (iCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source different = (some (.returned value),post)) :
    BitAnswer byte index value := by
  rw [shapes.2.2.2.2.2.2.1] at normal
  obtain ⟨inner,run,endpoint⟩ := declaration_return_word source post "j" (.const 0#64) 0#64 bitLoop value
    (by simp [eval,evalHOLExact]) normal
  have ready : BitInvariant byte (bind source "j" 0#64) := by
    refine ⟨0,by decide,bind_lookup_same _ _ _,?_,?_⟩
    · exact (bind_lookup_other source "j" "x" 0#64 (by decide)).trans xCell
    · intro prior before
      omega
  exact bit_loop_returned _ inner byte index ready
    ((bind_lookup_other source "j" "i" 0#64 (by decide)).trans iCell) value run

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_step_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_loop_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.different_returned
