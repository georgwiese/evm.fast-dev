import InitECandidate.Solver.Input.ScalarWordShape
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.ScalarLocals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Every live local is a scalar word; no memory-value premise is included. -/
def Words (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∀ name value,state.locals.lookup name=some value → ∃ word : BitVec 64,value=.val (.word word)

def Preserves (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Words source → Words (evaluateHOLFiniteState source program).2

theorem Words.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Words (emptyLocalsHOLFinite source) := by
  intro name value found
  change none=some value at found
  cases found

theorem Words.set (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : Words source) (name : MlS) (word : BitVec 64) :
    Words (setVarHOLFinite name (.val (.word word)) source) := by
  intro query value found
  by_cases same : query=name
  · subst query
    have actual : value=.val (.word word) := by simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE] using found.symm
    exact ⟨word,actual⟩
  · apply ready query value
    simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,same,Ne.symm same] using found

theorem Words.restore (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (before : Words source) (after : Words target) (name : MlS) :
    Words {target with locals:=HolFiniteMapExact.resVarEq target.locals (name,source.locals.lookup name)} := by
  intro query value found
  change (HolFiniteMapExact.resVarEq target.locals (name,source.locals.lookup name)).lookup query=some value at found
  rw [lookup_resVarEq_toExact] at found
  by_cases same : query=name
  · subst query
    cases saved : source.locals.lookup name with
    | none=>simp [resVarHOLExact,saved,FDOMSUB] at found
    | some previous=>
      have equal : previous=value := by simpa [resVarHOLExact,saved,FUPDATE] using found
      subst previous
      exact before name value saved
  · apply after query value
    cases saved : source.locals.lookup name <;> simpa [resVarHOLExact,saved,FUPDATE,FDOMSUB,same] using found

theorem assign (name : MlS) (expression : ExpHOL 64) : Preserves (.assign .local name expression) := by
  intro source ready
  classical
  rw [evaluateHOLFiniteState_assign]
  cases read : evalHOLExact source.toExact expression with
  | none=>exact ready
  | some value=>
    simp only
    split
    · rename_i valid
      cases previous : source.locals.lookup name with
      | none=>simp [isValidValueHOLExact,lookupKvarHOLExact,toExact,previous] at valid
      | some old=>
        obtain ⟨word,rfl⟩:=ready name old previous
        have typed : shapeOfHOLExact value=.one := by
          apply (shapeEqHOL_eq_true _ _).mp
          simpa [isValidValueHOLExact,lookupKvarHOLExact,toExact,previous,shapeOfHOLExact] using valid
        obtain ⟨next,rfl⟩:=scalar_word_of_shape value typed
        exact ready.set source name next
    · exact ready

theorem sequence (first second : ProgHOL 64) (front : Preserves first) (back : Preserves second) :
    Preserves (.seq first second) := by
  intro source ready
  have firstWords:=front source ready
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at firstWords ⊢
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>exact back middle firstWords
  | some result=>exact firstWords

theorem declared (name : MlS) (expression : ExpHOL 64) (body : ProgHOL 64) (tail : Preserves body) :
    Preserves (.dec name .one expression body) := by
  intro source ready
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · exact ready
  · rename_i value read
    split
    · rename_i checked
      have typed : shapeOfHOLExact value=.one := ((shapeEqHOL_eq_true _ _).mp checked).symm
      obtain ⟨word,rfl⟩:=scalar_word_of_shape value typed
      exact ready.restore source _ (tail _ (ready.set source name word)) name
    · exact ready

theorem loop (test : ExpHOL 64) (body : ProgHOL 64) (step : Preserves body) : Preserves (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory),source.clock=clock → Words source →
      Words (evaluateHOLFiniteState source (.while test body)).2 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock ih=>
      intro source clockEq ready
      rw [evaluateHOLFiniteState_while_total]
      generalize read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=value
      cases value with
      | none=>exact ready
      | some value=>
        cases value with
        | rStruct fields=>exact ready
        | nStruct name fields=>exact ready
        | val payload=>
          cases payload with
          | word word=>
            simp only
            by_cases nonzero : word≠0
            · rw [if_pos nonzero]
              by_cases zero : source.clock=0
              · rw [if_pos zero]; exact Words.empty source
              · rw [if_neg zero]
                have bodyWords:=step (decClockHOLFinite source) ready
                have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body=output at bodyWords forward ⊢
                obtain ⟨result,target⟩:=output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result forward]
                have earlier : target.clock<clock := by change target.clock≤source.clock-1 at forward; omega
                have rest:=ih target.clock earlier target rfl bodyWords
                cases result with
                | none=>exact rest
                | some result=>cases result <;> first | exact rest | exact bodyWords
            · rw [if_neg nonzero]; exact ready
  intro source ready
  exact auxiliary source.clock source rfl ready

end InitECandidate.Solver.Input.ScalarLocals

#print axioms InitECandidate.Solver.Input.ScalarLocals.assign
#print axioms InitECandidate.Solver.Input.ScalarLocals.declared
#print axioms InitECandidate.Solver.Input.ScalarLocals.loop
