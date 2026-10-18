import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Caller-control-safe prefixes including the original caught ignored calls.
Callees may throw; their installed handler is checked in the same grammar. -/
inductive HandledPrefix (key : MlS) : ProgHOL 64 → Prop where
  | base {program : ProgHOL 64} (safe : LocalPrefix key program) : HandledPrefix key program
  | caught (function : MlS) (arguments : List (ExpHOL 64)) (identifier parameter : MlS) {handler : ProgHOL 64}
      (other : key ≠ parameter) (safe : HandledPrefix key handler) :
      HandledPrefix key (.call (some (none, some (identifier, parameter, handler))) function arguments)
  | dec (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) {rest : ProgHOL 64}
      (other : key ≠ name) (tail : HandledPrefix key rest) : HandledPrefix key (.dec name shape expression rest)
  | seq {first second : ProgHOL 64} (left : HandledPrefix key first) (right : HandledPrefix key second) :
      HandledPrefix key (.seq first second)
  | ite (test : ExpHOL 64) {first second : ProgHOL 64} (left : HandledPrefix key first) (right : HandledPrefix key second) :
      HandledPrefix key (.ite test first second)

private theorem set_other {F : Type} (source : PanSemStateFiniteExact 64 F) (key name : MlS) (value : ValueHOL 64) (other : key ≠ name) :
    (setVarHOLFinite name value source).locals.lookup key = source.locals.lookup key := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm other]

private theorem restore_other (map : HolFiniteMapExact MlS (ValueHOL 64)) (key name : MlS) (value : Option (ValueHOL 64)) (other : key ≠ name) :
    (HolFiniteMapExact.resVarEq map (name, value)).lookup key = map.lookup key := by
  rw [lookup_resVarEq_toExact]
  cases value <;> simp [resVarHOLExact, other]

theorem HandledPrefix.summary_full {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : HandledPrefix key program) (source : PanSemStateFiniteExact 64 F) : LocalSummary key program source := by
  classical
  unfold LocalSummary
  induction safe generalizing source with
  | base safe => exact safe.summary_full source
  | caught function arguments identifier parameter other safe handlerIH =>
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source _) _ = output
          obtain ⟨result, target⟩ := output
          cases result with
          | none => simp
          | some result =>
            cases result with
            | returned returned => simp only; split <;> simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | finalFfi event => simp
            | exception exceptionId payload =>
              simp only
              by_cases matching : exceptionId = identifier
              · rw [if_pos matching]
                cases shapeRead : source.eshapes.lookup exceptionId with
                | none => simp
                | some shape =>
                  simp only
                  split
                  · let entered := setVarHOLFinite parameter payload {target with locals := source.locals}
                    have info := handlerIH entered
                    refine ⟨?_, info.2⟩
                    intro normal
                    exact (info.1 normal).trans (set_other _ key parameter payload other)
                  · simp
              · rw [if_neg matching]
                simp
  | dec name shape expression other tail tailIH =>
    rw [evaluateHOLFiniteState_dec_total]
    simp only
    split
    · simp
    · split
      · rename_i value read valid
        let declared := setVarHOLFinite name value source
        have info := tailIH declared
        refine ⟨?_, info.2⟩
        intro normal
        exact (restore_other _ key name _ other).trans ((info.1 normal).trans (set_other source key name value other))
      · simp
  | seq first second firstIH secondIH =>
    rw [evaluateHOLFiniteState_seq_line780]
    have info := firstIH source
    generalize computed : evaluateHOLFiniteState source _ = output at info ⊢
    obtain ⟨result, middle⟩ := output
    cases result with
    | none =>
      have frame := info.1 rfl
      have next := secondIH middle
      exact ⟨fun normal => (next.1 normal).trans frame, next.2⟩
    | some result => exact ⟨by simp, info.2⟩
  | ite test first second firstIH secondIH =>
    rw [evaluateHOLFiniteState_ite]
    generalize read : @evalHOLExact 64 F _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) test = observed
    cases observed with
    | none => simp
    | some value =>
      cases value with
      | val payload =>
        cases payload with
        | word word =>
          by_cases zero : word = 0
          · simpa only [if_pos zero] using secondIH source
          · simpa only [if_neg zero] using firstIH source
      | rStruct fields => simp
      | nStruct name fields => simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.HandledPrefix.summary_full
