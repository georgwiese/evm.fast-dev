import InitECandidate.Solver.Input.LocalPrefix
import Guest.Model
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual fall-through counter change, modulo the source word width.
This is a dataflow property and supplies no future execution. -/
def Advances (key : MlS) (amount : Nat) (program : ProgHOL 64) : Prop :=
  ∀ (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64),
    source.locals.lookup key = some (.val (.word word)) →
    evaluateHOLFiniteState source program = (none, post) →
    post.locals.lookup key = some (.val (.word (word + BitVec.ofNat 64 amount)))

theorem preserved (key : MlS) (program : ProgHOL 64) (safe : LocalPrefix key program) :
    Advances key 0 program := by
  intro source post word cell run
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [run] at summary
  simpa only [BitVec.add_zero] using (summary.1 rfl).trans cell

theorem increment (key : MlS) : Advances key 1 (.assign .local key (.op .add [.var .local key, .const 1#64])) := by
  intro source post word cell run
  have read : eval source (.op .add [.var .local key, .const 1#64]) = some (.val (.word (word + 1#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, cell, valueIsWord, valueWord, wordOpHOL, wordOp]
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign, read] at run
  have valid : isValidValueHOLFinite source .local key (.val (.word (word + 1#64))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, cell, shapeOfHOLExact, shapeEqHOL]
  simp only [← isValidValueHOLFinite_eq, valid, ↓reduceIte, setKvarHOLFinite] at run
  have postEq := congrArg Prod.snd run
  change setVarHOLFinite key (.val (.word (word + 1#64))) source = post at postEq
  rw [← postEq]
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem sequence (key : MlS) (first second : ProgHOL 64) (left right : Nat)
    (front : Advances key left first) (back : Advances key right second) :
    Advances key (left + right) (.seq first second) := by
  intro source post word cell run
  obtain ⟨middle, firstRun, secondRun⟩ := Input.sequence_none source post first second run
  have next := back middle post (word + BitVec.ofNat 64 left) (front source middle word cell firstRun) secondRun
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using next

private theorem other_set (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key name : MlS)
    (value : ValueHOL 64) (other : key ≠ name) :
    (setVarHOLFinite name value source).locals.lookup key = source.locals.lookup key := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm other]

private theorem other_restore (map : HolFiniteMapExact MlS (ValueHOL 64)) (key name : MlS)
    (value : Option (ValueHOL 64)) (other : key ≠ name) :
    (HolFiniteMapExact.resVarEq map (name, value)).lookup key = map.lookup key := by
  rw [lookup_resVarEq_toExact]
  cases value <;> simp [resVarHOLExact, other]

/-- An unrelated lexical binding preserves actual counter progress through
its real continuing body and restoration. -/
theorem declared (key name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64)
    (body : ProgHOL 64) (amount : Nat) (other : key ≠ name)
    (tail : Advances key amount body) : Advances key amount (.dec name shape expression body) := by
  intro source post word cell run
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only at run
  split at run
  · cases run
  · rename_i value read
    split at run
    · generalize bodyRun : evaluateHOLFiniteState (setVarHOLFinite name value source) body = output at run
      obtain ⟨result, inner⟩ := output
      have resultEq := congrArg Prod.fst run
      change result = none at resultEq
      have postEq := congrArg Prod.snd run
      change {inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, source.locals.lookup name)} = post at postEq
      have actual : evaluateHOLFiniteState (setVarHOLFinite name value source) body = (none, inner) := by
        rw [bodyRun, resultEq]
      have before := (other_set source key name value other).trans cell
      have after := tail _ inner word before actual
      rw [← postEq]
      exact (other_restore _ key name _ other).trans after
    · cases run

/-- Real scoped helper calls restore the caller's counter before their
continuation, regardless of callee effects and local bindings. -/
theorem scoped_call (key : MlS) (name : String) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL 64)) (body : ProgHOL 64) (amount : Nat)
    (other : key ≠ ofString name) (tail : Advances key amount body) :
    Advances key amount (.decCall (ofString name) shape function arguments body) := by
  classical
  intro source post word cell run
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at run; cases run
  | some values =>
    simp only [args] at run
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at run; cases run
    | some data =>
      obtain ⟨actualBody, callee, returnShape⟩ := data
      simp only [called] at run
      by_cases zero : source.clock = 0
      · rw [if_pos zero] at run
        cases run
      · rw [if_neg zero] at run
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actualBody = output at run
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases run
        | some result =>
          cases result with
          | returned returned =>
            simp only at run
            split at run
            · change (let output := evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) body
                (output.1, restore source name output.2)) = (none, post) at run
              generalize continuationRun : evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) body = output at run
              obtain ⟨result, inner⟩ := output
              have resultEq := congrArg Prod.fst run
              change result = none at resultEq
              have postEq := congrArg Prod.snd run
              change restore source name inner = post at postEq
              have nextCell : (CallNormal.continuationEntry source target name returned).locals.lookup key = some (.val (.word word)) :=
                (other_set _ key (ofString name) returned other).trans cell
              have bodyRun : evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) body = (none, inner) := by
                rw [continuationRun, resultEq]
              have next := tail _ inner word nextCell bodyRun
              rw [← postEq]
              exact (other_restore _ key (ofString name) _ other).trans next
            · cases run
          | error => cases run
          | timeOut => cases run
          | «break» => cases run
          | «continue» => cases run
          | exception identifier payload => cases run
          | finalFfi event => cases run

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.preserved
#print axioms InitECandidate.Solver.Input.CounterFlow.increment
#print axioms InitECandidate.Solver.Input.CounterFlow.sequence
#print axioms InitECandidate.Solver.Input.CounterFlow.scoped_call
#print axioms InitECandidate.Solver.Input.CounterFlow.declared
