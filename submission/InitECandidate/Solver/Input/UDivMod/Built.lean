import InitECandidate.Solver.Input.UDivMod.Setup

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete literal unsigned division with a nonzero divisor. Includes the
early return and all64 loop rounds, without changing memory or control. -/
theorem body_execute_nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (nonzero : b≠0#64) (enough : 64≤source.clock) :
    ∃ target q r paid,paid≤64 ∧ evaluateHOLFiniteState source body=(some (.returned (pairValue q r)),target) ∧
      target.clock=source.clock-paid ∧ frozen target=frozen source := by
  classical
  have zeroRead : eval source zeroTest=some (.val (.word 0#64)) := by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  have zeroRun : evaluateHOLFiniteState source zeroGuard=(none,source) := by
    simp only [eval] at zeroRead
    rw [zeroGuard,evaluateHOLFiniteState_ite,zeroRead]
    simp
  have smallRead : eval source smallTest=some (.val (.word (if a.toNat<b.toNat then 1#64 else 0#64))) := by
    simp [eval,smallTest,localVar,evalHOLExact,toExact,aLocal,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  simp only [eval] at smallRead
  by_cases small : a.toNat<b.toNat
  · have smallRun : evaluateHOLFiniteState source smallGuard=(some (.returned (pairValue 0#64 a)),emptyLocalsHOLFinite source) := by
      rw [smallGuard,evaluateHOLFiniteState_ite,smallRead]
      simp only [if_pos small]
      simp [pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,aLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨emptyLocalsHOLFinite source,0#64,a,0,by decide,?_,by simp [emptyLocalsHOLFinite],by rfl⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ zeroRun (Nat.le_refl _)]
    exact WitnessRadix.StateSteps.stopped_sequence source _ smallGuard setupProgram (.returned (pairValue 0#64 a)) smallRun (Nat.le_refl _)
  · have smallRun : evaluateHOLFiniteState source smallGuard=(none,source) := by
      rw [smallGuard,evaluateHOLFiniteState_ite,smallRead]
      simp only [if_neg small]
      simp
    obtain ⟨target,q,r,setupRun,clock,frame⟩:=setup_execute source a b aLocal bLocal enough
    refine ⟨target,q,r,64,by decide,?_,clock,frame⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ zeroRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence source source _ _ smallRun (Nat.le_refl _)]
    exact setupRun

def values (a b : BitVec 64) : List (ValueHOL 64) := [.val (.word a),.val (.word b)]
def rawLocals (a b : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "b" then some (.val (.word b)) else if name=ofString "a" then some (.val (.word a)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : BitVec 64)
    (lookup : codeFn (ofString "udivmod")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "udivmod") (values a b)=some (body,callee,returnShape) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "b")=some (.val (.word b)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values a b).length ∧
      ((formals.zip (values a b)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "udivmod") (values a b)=some (body,rawLocals a b,returnShape) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a"≠ofString "b" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.body_execute_nonzero
#print axioms InitECandidate.Solver.Input.UDivMod.environment
