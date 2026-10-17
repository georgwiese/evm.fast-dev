import InitECandidate.Solver.MutableTable.MemeqSizedProgram
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.MutableTable.MemeqSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def alignedProgram : ProgHOL 64 := .seq (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip)
  (.seq (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip) Memeq32.parts.otherAligned)
def afterDeclaration : ProgHOL 64 := .seq (.ite Memeq32.alignmentTest alignedProgram .skip) Memeq32.parts.tailCode

theorem body_shape : Memeq32.body = .dec (ofString "i") .one (.const 0#64) afterDeclaration := Memeq32.body_shape

/-- Actual whole aligned20/52-byte comparison function, with every mismatch
and success return and outer scope. Its fast paths have no body clock charge.
Actual read/alignment premises are explicit and discharged by owned reads. -/
theorem aligned_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind)
    (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8)
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (aligned : eval (WitnessRadix.QueryBranch.bind source "i" 0#64) Memeq32.alignmentTest = some (.val (.word 1#64)))
    (ready : ∀ check ∈ checks kind left right leftBytes rightBytes,
      CompareChain.Ready (WitnessRadix.QueryBranch.bind source "i" 0#64) check) :
    evaluateHOLFiniteState source Memeq32.body =
      (some (.returned (.val (.word (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64)))),
        restore source "i" (emptyLocalsHOLFinite (WitnessRadix.QueryBranch.bind source "i" 0#64))) := by
  let loaded := WitnessRadix.QueryBranch.bind source "i" 0#64
  let answer : ValueHOL 64 := .val (.word (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64))
  have length' : loaded.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))) :=
    (bind_lookup_other _ "i" "n" _ (by decide)).trans length
  have fast : evaluateHOLFiniteState loaded (selectedBranch kind) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := branch_execute loaded kind left right leftBytes rightBytes ready
  have fullAligned : evaluateHOLFiniteState loaded alignedProgram = (some (.returned answer), emptyLocalsHOLFinite loaded) := by
    cases kind with
    | address =>
      have choose : evaluateHOLFiniteState loaded (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip) =
          (some (.returned answer), emptyLocalsHOLFinite loaded) := by
        rw [evaluateHOLFiniteState_ite]
        simpa [Memeq32.sizeTest, localVar, evalHOLExact, toExact, length', keySize, HashSized.keySize,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, selectedBranch] using fast
      exact StateSteps.stopped_sequence loaded _ _ _ (.returned answer) choose (Nat.le_refl _)
    | storage =>
      have skipTwenty : evaluateHOLFiniteState loaded (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip) = (none, loaded) := by
        rw [evaluateHOLFiniteState_ite]
        simp [Memeq32.sizeTest, localVar, evalHOLExact, toExact, length', keySize, HashSized.keySize,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
      have skipThirtyTwo : evaluateHOLFiniteState loaded (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip) = (none, loaded) := by
        rw [evaluateHOLFiniteState_ite]
        simp [Memeq32.sizeTest, localVar, evalHOLExact, toExact, length', keySize, HashSized.keySize,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
      have choose : evaluateHOLFiniteState loaded (.ite (Memeq32.sizeTest 52#64) fiftyTwo .skip) =
          (some (.returned answer), emptyLocalsHOLFinite loaded) := by
        rw [evaluateHOLFiniteState_ite]
        simpa [Memeq32.sizeTest, localVar, evalHOLExact, toExact, length', keySize, HashSized.keySize,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, selectedBranch] using fast
      have other : evaluateHOLFiniteState loaded Memeq32.parts.otherAligned = (some (.returned answer), emptyLocalsHOLFinite loaded) := by
        rw [other_shape]
        exact StateSteps.stopped_sequence loaded _ (.ite (Memeq32.sizeTest 52#64) fiftyTwo .skip) alignedLoops (.returned answer) choose (Nat.le_refl _)
      rw [alignedProgram, StateSteps.next_sequence loaded loaded _ _ skipTwenty (Nat.le_refl _),
        StateSteps.next_sequence loaded loaded _ _ skipThirtyTwo (Nat.le_refl _)]
      exact other
  have selected : evaluateHOLFiniteState loaded (.ite Memeq32.alignmentTest alignedProgram .skip) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := by
    simp only [eval] at aligned
    rw [evaluateHOLFiniteState_ite]
    simpa [loaded, aligned] using fullAligned
  have tailUnreachable := StateSteps.stopped_sequence loaded (emptyLocalsHOLFinite loaded)
    (.ite Memeq32.alignmentTest alignedProgram .skip) Memeq32.parts.tailCode (.returned answer) selected (Nat.le_refl _)
  change evaluateHOLFiniteState loaded afterDeclaration = _ at tailUnreachable
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "i" (.const 0#64) 0#64 afterDeclaration _ rfl tailUnreachable

end InitECandidate.Solver.MutableTable.MemeqSized

#print axioms InitECandidate.Solver.MutableTable.MemeqSized.body_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.aligned_execute
