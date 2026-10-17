import InitECandidate.Solver.Arenas.Prefix
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.Arenas.Prefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix (Action)

theorem Executes.append {F : Type} {direction : Direction} {source middle target : PanSemStateFiniteExact 64 F}
    {first rest : List Action} {restoreFirst restoreRest : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (head : Executes direction source first middle restoreFirst)
    (tail : Executes direction middle rest target restoreRest) :
    Executes direction source (first ++ rest) target (fun post => restoreFirst (restoreRest post)) := by
  induction head with
  | done source => exact tail
  | declare word read next ih => exact .declare word read (ih tail)
  | allocate pointer limit amount read code pointerGlobal limitGlobal aligned room enough next ih =>
    exact .allocate pointer limit amount read code pointerGlobal limitGlobal aligned room enough (ih tail)
  | command run clock next ih => exact .command run clock (ih tail)

/-- Reflect a genuine normal command-sequence execution into prefix evidence.
The canonical evaluator supplies the clock monotonicity of each real command. -/
theorem commands_execute {F : Type} (direction : Direction) (source target : PanSemStateFiniteExact 64 F)
    (commands : List (ProgHOL 64))
    (run : evaluateHOLFiniteState source (program direction (commands.map Action.command) .skip) = (none, target)) :
    Executes direction source (commands.map Action.command) target id := by
  induction commands generalizing source with
  | nil =>
    simp only [List.map_nil, program, evaluateHOLFiniteState_skip] at run
    have same := congrArg Prod.snd run
    change source = target at same
    subst target
    exact .done source
  | cons command rest ih =>
    simp only [List.map_cons, program] at run
    rw [evaluateHOLFiniteState_seq_line780] at run
    generalize computed : evaluateHOLFiniteState source command = output at run
    obtain ⟨result, middle⟩ := output
    cases result with
    | none =>
      have clock := evaluateHOLFiniteState_clock_le source command
      rw [computed] at clock
      exact .command computed clock (ih middle run)
    | some result => cases congrArg Prod.fst run

def fieldCommands (baseName messageName : String) (fields : List FieldStores.Field) : List (ProgHOL 64) :=
  fields.map (fun field => .store (FieldStores.address baseName field.offset) (field.value.expression messageName))
def fieldActions (baseName messageName : String) (fields : List FieldStores.Field) : List Action :=
  (fieldCommands baseName messageName fields).map Action.command

theorem field_program (direction : Direction) (baseName messageName : String) (fields : List FieldStores.Field)
    (continuation : ProgHOL 64) :
    program direction (fieldActions baseName messageName fields) continuation =
      FieldStores.program baseName messageName fields continuation := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    simpa only [fieldActions, fieldCommands, List.map_cons, program, FieldStores.program] using
      congrArg (fun tail => ProgHOL.seq (.store (FieldStores.address baseName field.offset)
        (field.value.expression messageName)) tail) ih

/-- Use proved actual field stores as a constructor-prefix segment. -/
theorem field_stores {F : Type} (direction : Direction) (source : PanSemStateFiniteExact 64 F)
    (baseName messageName : String) (base message : BitVec 64) (fields : List FieldStores.Field)
    (baseLocal : source.locals.lookup (ofString baseName) = some (.val (.word base)))
    (ready : ∀ field ∈ fields, field.value.Ready source messageName message)
    (mapped : ∀ field ∈ fields, source.memaddrs (base + BitVec.ofNat 64 field.offset))
    (separate : ∀ reader ∈ fields, ∀ writer ∈ fields,
      reader.value.Avoid message (base + BitVec.ofNat 64 writer.offset)) :
    Executes direction source (fieldActions baseName messageName fields)
      {source with memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes base fields)} id := by
  have run := FieldStores.execute source baseName messageName base message fields baseLocal ready mapped separate .skip
  rw [evaluateHOLFiniteState_skip] at run
  apply commands_execute direction source _ (fieldCommands baseName messageName fields)
  rw [← field_program direction baseName messageName fields .skip] at run
  exact run

end InitECandidate.Solver.Arenas.Prefix

#print axioms InitECandidate.Solver.Arenas.Prefix.Executes.append
#print axioms InitECandidate.Solver.Arenas.Prefix.commands_execute
#print axioms InitECandidate.Solver.Arenas.Prefix.field_program
#print axioms InitECandidate.Solver.Arenas.Prefix.field_stores
