import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Input.ReturnFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def Returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
    (property : ValueHOL 64 → Prop) : Prop :=
  ∀ target value,evaluateHOLFiniteState source program=(some (.returned value),target) → property value

theorem skip (source : PanSemStateFiniteExact 64 Guest.HostMemory) (property : ValueHOL 64 → Prop) : Returns source .skip property := by
  intro target value normal
  rw [evaluateHOLFiniteState_skip] at normal
  cases normal

theorem returned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64)
    (expected : ValueHOL 64) (property : ValueHOL 64 → Prop)
    (read : eval source expression=some expected) (fact : property expected) : Returns source (.return expression) property := by
  intro target value normal
  have actual := (Input.return_normal source target expression value normal).1
  have same : expected=value := Option.some.inj (read.symm.trans actual)
  rwa [← same]

theorem conditional (source : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (yes no : ProgHOL 64) (property : ValueHOL 64 → Prop)
    (left : Returns source yes property) (right : Returns source no property) : Returns source (.ite test yes no) property := by
  intro target value normal
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = read at normal
  cases read with
  | none => cases normal
  | some read =>
    cases read with
    | rStruct fields => cases normal
    | nStruct name fields => cases normal
    | val payload =>
      cases payload with
      | word word =>
        by_cases zero : word=0
        · exact right target value (by simpa only [if_pos zero] using normal)
        · exact left target value (by simpa only [if_neg zero] using normal)

theorem sequence (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (property : ValueHOL 64 → Prop) (front : Returns source first property)
    (back : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → Returns middle second property) :
    Returns source (.seq first second) property := by
  intro target value normal
  rw [evaluateHOLFiniteState_seq_line780] at normal
  generalize computed : evaluateHOLFiniteState source first=output at normal
  obtain ⟨result,middle⟩ := output
  cases result with
  | none => exact back middle computed target value normal
  | some result =>
    have resultEq := congrArg Prod.fst normal
    have actual : result=.returned value := by simpa only [Option.some.injEq] using resultEq
    rw [actual] at computed
    exact front middle value computed

theorem declared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (property : ValueHOL 64 → Prop)
    (tail : ∀ value,Returns (setVarHOLFinite name value source) body property) :
    Returns source (.dec name shape expression body) property := by
  intro target value normal
  rw [evaluateHOLFiniteState_dec_total] at normal
  simp only at normal
  split at normal
  · cases normal
  · rename_i declared read
    split at normal
    · have resultEq := congrArg Prod.fst normal
      exact tail declared (evaluateHOLFiniteState (setVarHOLFinite name declared source) body).2 value (Prod.ext resultEq rfl)
    · cases normal

end InitECandidate.Solver.Input.ReturnFacts

#print axioms InitECandidate.Solver.Input.ReturnFacts.skip
#print axioms InitECandidate.Solver.Input.ReturnFacts.returned
#print axioms InitECandidate.Solver.Input.ReturnFacts.conditional
#print axioms InitECandidate.Solver.Input.ReturnFacts.sequence
#print axioms InitECandidate.Solver.Input.ReturnFacts.declared
