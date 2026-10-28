import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.LocalEffectsCall
import InitECandidate.Solver.Input.ScalarShape

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Dynamic arguments may fail. Any real checked scalar return resumes
the original caller locals with exactly one new word binding, so a suffix
can derive its own current local facts without a future-success premise. -/
theorem scalar_scope_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (function : MlS)
    (arguments : List (ExpHOL 64)) (formals : List (MlS×ShapeHOL)) (body continuation : ProgHOL 64)
    (returnShape : ShapeHOL) (calleePrice tailPrice : Nat)
    (code : source.code.lookup function=some (formals,body,returnShape))
    (priced : Bound source.code body calleePrice)
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ word : BitVec 64,target.code=source.code→
      target.clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word word))) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one function arguments continuation)).2.clock≤calleePrice+tailPrice+1:=by
  cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
  | none=>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
    simp only
    omega
  | some values=>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
      simp only
      rw [called]
      simp only
      omega
    | some data=>
      obtain ⟨actual,callee,shape⟩:=data
      have same:=LocalEffects.lookup_body source.code function formals body returnShape code values actual callee shape called
      subst actual
      apply scoped_reached_current source name .one function arguments values body continuation callee shape calleePrice tailPrice args called
        (priced (callEntryStateHOLFinite source callee) rfl)
      intro target returned run checked
      have typed : shapeOfHOLExact returned=.one:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
      obtain ⟨word,rfl⟩:=ScalarShape.word returned typed
      exact tail target word ((evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned (.val (.word word)))) run).2.2.2)

theorem scalar_declaration_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (expression : ExpHOL 64) (body : ProgHOL 64) (price : Nat)
    (tail : ∀ word : BitVec 64,(setVarHOLFinite name (.val (.word word)) source).clock-
      (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) source) body).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.dec name .one expression body)).2.clock≤price:=by
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i value read
    split
    · rename_i checked
      have typed : shapeOfHOLExact value=.one:=((shapeEqHOL_eq_true _ _).mp checked).symm
      obtain ⟨word,rfl⟩:=ScalarShape.word value typed
      exact tail word
    · simp

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scalar_scope_current
#print axioms InitECandidate.Solver.Input.ClockCost.scalar_declaration_current
