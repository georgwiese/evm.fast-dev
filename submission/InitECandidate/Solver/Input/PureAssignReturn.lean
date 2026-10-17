import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual pure scalar call assigning an existing local, with its real shape
check and canonical caller state. No lexical declaration is substituted. -/
theorem pure_assign_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (old : BitVec 64) (fn : MlS)
    (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (word : BitVec 64) (paid : Nat)
    (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (lookup : lookupCodeHOLFinite source.code.lookup fn values=some (body,callee,.one)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned (.val (.word word))),target))
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}) :
    evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) fn expressions)=
      (none,bind {source with clock:=source.clock-1-paid} name word) := by
  classical
  have valid : isValidValueHOLFinite source .local (ofString name) (.val (.word word))=true := by
    simp [isValidValueHOLFinite,lookupKvarHOLFinite,present,shapeOfHOLExact,shapeEqHOL]
  have actual:=evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none fn expressions values body callee .one
    (.val (.word word)) target args lookup (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL]) (by simpa only [isValidValueHOLFinite_eq] using valid)
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have targetEq : setKvarHOLFinite .local (ofString name) (.val (.word word)) {target with locals:=source.locals}=
      bind {source with clock:=source.clock-1-paid} name word :=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) (.val (.word word)) state) callerFrame
  rw [targetEq] at actual
  exact actual

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.pure_assign_execute
