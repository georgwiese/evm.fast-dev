import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.WitnessRadix.ZeroCall

namespace InitECandidate.Solver.WitnessRadix.ProgramPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

inductive Action where
  | declare (name : String) (expression : ExpHOL 64)
  | allocate (name : String) (expression : ExpHOL 64)
  | command (code : ProgHOL 64)

def program : List Action → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | .declare name expression :: rest, continuation => .dec (ofString name) .one expression (program rest continuation)
  | .allocate name expression :: rest, continuation =>
      .decCall (ofString name) .one (ofString "alloc") [expression] (program rest continuation)
  | .command code :: rest, continuation => .seq code (program rest continuation)

/-- Compositional evidence for actual local declarations, actual allocator
calls and nonreturning commands. Every lexical restoration is retained. -/
inductive Executes {F : Type} : PanSemStateFiniteExact 64 F → List Action → PanSemStateFiniteExact 64 F →
    (PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F) → Prop
  | done (source) : Executes source [] source id
  | declare {source entered name expression rest restoreRest} (word : BitVec 64)
      (read : eval source expression = some (.val (.word word)))
      (next : Executes (bind source name word) rest entered restoreRest) :
      Executes source (.declare name expression :: rest) entered (fun target => restore source name (restoreRest target))
  | allocate {source entered name expression rest restoreRest} (pointer amount : BitVec 64)
      (read : eval source expression = some (.val (.word amount)))
      (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
      (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
      (fits : pointer.toNat + amount.toNat ≤ 33806089496) (enough : 1 ≤ source.clock)
      (next : Executes (bind (PersistentAlloc.post { source with clock := source.clock - 1 } pointer amount) name pointer)
        rest entered restoreRest) :
      Executes source (.allocate name expression :: rest) entered (fun target => restore source name (restoreRest target))
  | command {source post entered code rest restoreRest}
      (run : evaluateHOLFiniteState source code = (none, post)) (clock : post.clock ≤ source.clock)
      (next : Executes post rest entered restoreRest) : Executes source (.command code :: rest) entered restoreRest

theorem execute {F : Type} {source entered : PanSemStateFiniteExact 64 F} {actions : List Action}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Executes source actions entered restoreStack) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program actions continuation) =
      (let output := evaluateHOLFiniteState entered continuation; (output.1, restoreStack output.2)) := by
  classical
  induction setup with
  | done source => rfl
  | @declare source entered name expression rest restoreRest word read next ih =>
    have localSetup : BuildEntry.Initializes source [(name, expression)] (bind source name word)
        (fun target => restore source name target) := .step word read (.done _)
    have localRun := BuildEntry.declarations_execute localSetup (program rest continuation)
    change evaluateHOLFiniteState source (.dec (ofString name) .one expression (program rest continuation)) = _ at localRun
    rw [program, localRun, ih]
  | @allocate source entered name expression rest restoreRest pointer amount read code heapGlobal fits enough next ih =>
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [expression] = some (PersistentAlloc.values amount) := by
      simp only [eval] at read
      simp [evalListHOLFinite, evalListHOLExact, read, PersistentAlloc.values]
    rw [program, PersistentAlloc.call_execute source name [expression] (program rest continuation)
      pointer amount args code heapGlobal fits enough, ih]
  | command run clock next ih =>
    rw [program, StateSteps.next_sequence _ _ _ _ run clock, ih]

theorem restoration_frame {F : Type} {source entered : PanSemStateFiniteExact 64 F} {actions : List Action}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Executes source actions entered restoreStack) (target : PanSemStateFiniteExact 64 F) :
    emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target := by
  induction setup with
  | done source => rfl
  | declare word read next ih => exact ih
  | allocate pointer amount read code heapGlobal fits enough next ih => exact ih
  | command run clock next ih => exact ih

end InitECandidate.Solver.WitnessRadix.ProgramPrefix

#print axioms InitECandidate.Solver.WitnessRadix.ProgramPrefix.execute
#print axioms InitECandidate.Solver.WitnessRadix.ProgramPrefix.restoration_frame
