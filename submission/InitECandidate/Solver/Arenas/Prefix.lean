import InitECandidate.Solver.Arenas.Calls
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Arenas.Prefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix (Action)

/-- The shared constructor-action syntax instantiated with the actual arena
allocator. It is used to prove unchanged scratch constructors. -/
def program (direction : Direction) : List Action → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | .declare name expression :: rest, continuation =>
      .dec (ofString name) .one expression (program direction rest continuation)
  | .allocate name expression :: rest, continuation =>
      .decCall (ofString name) .one (ofString (functionName direction)) [expression] (program direction rest continuation)
  | .command code :: rest, continuation => .seq code (program direction rest continuation)

inductive Executes {F : Type} (direction : Direction) : PanSemStateFiniteExact 64 F → List Action →
    PanSemStateFiniteExact 64 F → (PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F) → Prop where
  | done (source) : Executes direction source [] source id
  | declare {source entered name expression rest restoreRest} (word : BitVec 64)
      (read : eval source expression = some (.val (.word word)))
      (next : Executes direction (WitnessRadix.QueryBranch.bind source name word) rest entered restoreRest) :
      Executes direction source (.declare name expression :: rest) entered (fun target => restore source name (restoreRest target))
  | allocate {source entered name expression rest restoreRest} (pointer limit amount : BitVec 64)
      (read : eval source expression = some (.val (.word amount)))
      (code : source.code.lookup (ofString (functionName direction)) = some (formals, body direction, .one))
      (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
      (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
      (aligned : limit.toNat % 8 = 0) (room : Room direction pointer limit amount) (enough : 1 ≤ source.clock)
      (next : Executes direction
        (WitnessRadix.QueryBranch.bind (post {source with clock := source.clock - 1} direction pointer amount)
          name (resultWord direction pointer amount)) rest entered restoreRest) :
      Executes direction source (.allocate name expression :: rest) entered (fun target => restore source name (restoreRest target))
  | command {source post entered code rest restoreRest}
      (run : evaluateHOLFiniteState source code = (none, post)) (clock : post.clock ≤ source.clock)
      (next : Executes direction post rest entered restoreRest) :
      Executes direction source (.command code :: rest) entered restoreRest

theorem execute {F : Type} {direction : Direction} {source entered : PanSemStateFiniteExact 64 F}
    {actions : List Action} {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Executes direction source actions entered restoreStack) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program direction actions continuation) =
      (let output := evaluateHOLFiniteState entered continuation; (output.1, restoreStack output.2)) := by
  classical
  induction setup with
  | done source => rfl
  | @declare source entered name expression rest restoreRest word read next ih =>
    have localSetup : WitnessRadix.BuildEntry.Initializes source [(name, expression)]
        (WitnessRadix.QueryBranch.bind source name word) (fun target => restore source name target) :=
      .step word read (.done _)
    have localRun := WitnessRadix.BuildEntry.declarations_execute localSetup (program direction rest continuation)
    change evaluateHOLFiniteState source (.dec (ofString name) .one expression (program direction rest continuation)) = _ at localRun
    rw [program, localRun, ih]
  | @allocate source entered name expression rest restoreRest pointer limit amount read code pointerGlobal limitGlobal aligned room enough next ih =>
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [expression] = some [.val (.word amount)] := by
      simp only [eval] at read
      simp only [evalListHOLFinite, evalListHOLExact, read]
    rw [program, Arenas.call_execute source direction name [expression] (program direction rest continuation)
      pointer limit amount args code pointerGlobal limitGlobal aligned room enough, ih]
  | command run clock next ih =>
    rw [program, WitnessRadix.StateSteps.next_sequence _ _ _ _ run clock, ih]

theorem restoration_frame {F : Type} {direction : Direction} {source entered : PanSemStateFiniteExact 64 F}
    {actions : List Action} {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Executes direction source actions entered restoreStack) (target : PanSemStateFiniteExact 64 F) :
    emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target := by
  induction setup with
  | done source => rfl
  | declare word read next ih => exact ih
  | allocate pointer limit amount read code pointerGlobal limitGlobal aligned room enough next ih => exact ih
  | command run clock next ih => exact ih

end InitECandidate.Solver.Arenas.Prefix

#print axioms InitECandidate.Solver.Arenas.Prefix.execute
#print axioms InitECandidate.Solver.Arenas.Prefix.restoration_frame
