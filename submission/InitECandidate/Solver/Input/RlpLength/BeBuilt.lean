import InitECandidate.Solver.Input.RlpLength.BeLoop

namespace InitECandidate.Solver.Input.RlpLength.Be
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem execute_exact (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (v : source.locals.lookup (ofString "v")=some (.val (.word value))) (enough : 8≤source.clock) :
    ∃ target count,count=byteCount 8 value ∧ count≤8 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 count)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-count} := by
  classical
  let entry:=bind source "n" 0#64
  have entryV : entry.locals.lookup (ofString "v")=some (.val (.word value)):=(bind_lookup_other source "n" "v" _ (by decide)).trans v
  have entryN : entry.locals.lookup (ofString "n")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  obtain ⟨loopPost,count,exactCount,bound,loopRun,loopEq,finalN⟩:=loop_execute_exact entry value 0 8 value.isLt (by decide) enough entryV entryN
  simp only [Nat.zero_add] at finalN
  have returnRun : evaluateHOLFiniteState loopPost returnCount=(some (.returned (.val (.word (BitVec.ofNat 64 count)))),emptyLocalsHOLFinite loopPost) := by
    simp [returnCount,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,finalN,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState entry initializedTail=(some (.returned (.val (.word (BitVec.ofNat 64 count)))),emptyLocalsHOLFinite loopPost) := by
    have loopClock:=congrArg PanSemStateFiniteExact.clock loopEq
    change loopPost.clock=source.clock-count at loopClock
    rw [initializedTail,WitnessRadix.StateSteps.next_sequence entry loopPost _ _ loopRun (by change loopPost.clock≤source.clock; omega)]
    exact returnRun
  have scopeRun:=ScalarScope.declare_execute source (emptyLocalsHOLFinite loopPost) "n" (.const 0#64) 0#64 initializedTail
    (some (.returned (.val (.word (BitVec.ofNat 64 count))))) rfl tailRun
  refine ⟨restore source "n" (emptyLocalsHOLFinite loopPost),count,exactCount,bound,?_,?_⟩
  · rw [body_shape]
    exact scopeRun
  · change emptyLocalsHOLFinite loopPost=emptyLocalsHOLFinite {source with clock:=source.clock-count}
    rw [loopEq]
    rfl

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (v : source.locals.lookup (ofString "v")=some (.val (.word value))) (enough : 8≤source.clock) :
    ∃ target count,count≤8 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 count)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-count} := by
  obtain ⟨target,count,_exactCount,bounded,run,frame⟩:=execute_exact source value v enough
  exact ⟨target,count,bounded,run,frame⟩

def values (value : BitVec 64) : List (ValueHOL 64) := [.val (.word value)]
def rawLocals (value : BitVec 64) (name : MlS) : Option (ValueHOL 64) := if name=ofString "v" then some (.val (.word value)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (value : BitVec 64)
    (lookup : codeFn (ofString "rlp_be_len")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "rlp_be_len") (values value)=some (body,callee,.one) ∧
      callee.lookup (ofString "v")=some (.val (.word value)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values value).length ∧
      ((formals.zip (values value)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_be_len") (values value)=some (body,rawLocals value,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [rawLocals]

end InitECandidate.Solver.Input.RlpLength.Be

#print axioms InitECandidate.Solver.Input.RlpLength.Be.execute
#print axioms InitECandidate.Solver.Input.RlpLength.Be.environment

#print axioms InitECandidate.Solver.Input.RlpLength.Be.execute_exact
