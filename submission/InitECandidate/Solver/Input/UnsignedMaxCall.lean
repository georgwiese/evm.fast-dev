import InitECandidate.Solver.Input.CeilLog2Call

namespace InitECandidate.Solver.Input.UnsignedMax
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_max with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",.one),(ofString "b",.one)]
def test : ExpHOL 64 := .cmp .lower (localVar "b") (localVar "a")
def guard : ProgHOL 64 := .ite test (.return (localVar "a")) .skip
def selected (a b : BitVec 64) := if b.toNat<a.toNat then a else b

theorem body_shape : body=.seq guard (.return (localVar "b")) := by
  simp only [body,Guest.guestFn_max,progToHOL,expToHOL,guard,test,localVar]

theorem selected_number (a b : BitVec 64) : (selected a b).toNat=max a.toNat b.toNat := by
  by_cases greater : b.toNat<a.toNat
  · simp only [selected,if_pos greater]; omega
  · simp only [selected,if_neg greater]; omega

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (selected a b)))),emptyLocalsHOLFinite source) := by
  have read : eval source test=some (.val (.word (if b.toNat<a.toNat then 1#64 else 0#64))) := by
    simp [eval,test,localVar,evalHOLExact,toExact,aLocal,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  have returnA : evaluateHOLFiniteState source (.return (localVar "a"))=(some (.returned (.val (.word a))),emptyLocalsHOLFinite source) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,aLocal,shapeOfHOLExact]
  have returnB : evaluateHOLFiniteState source (.return (localVar "b"))=(some (.returned (.val (.word b))),emptyLocalsHOLFinite source) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,bLocal,shapeOfHOLExact]
  simp only [eval] at read
  by_cases greater : b.toNat<a.toNat
  · have guarded : evaluateHOLFiniteState source guard=(some (.returned (.val (.word a))),emptyLocalsHOLFinite source) := by
      rw [guard,evaluateHOLFiniteState_ite,read]
      simp only [if_pos greater]
      exact returnA
    rw [body_shape,selected,if_pos greater]
    exact StateSteps.stopped_sequence source _ guard (.return (localVar "b")) (.returned (.val (.word a))) guarded (Nat.le_refl _)
  · have guarded : evaluateHOLFiniteState source guard=(none,source) := by
      rw [guard,evaluateHOLFiniteState_ite,read]
      simp [greater,evaluateHOLFiniteState_skip]
    rw [body_shape,StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _),selected,if_neg greater]
    exact returnB

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "max")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 27 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_max) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_max,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def values (a b : BitVec 64) : List (ValueHOL 64) := [.val (.word a),.val (.word b)]
def rawLocals (a b : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "b" then some (.val (.word b)) else if name=ofString "a" then some (.val (.word a)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : BitVec 64)
    (code : codeFn (ofString "max")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "max") (values a b)=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "b")=some (.val (.word b)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values a b).length ∧
      ((formals.zip (values a b)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "max") (values a b)=some (body,rawLocals a b,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "a"≠ofString "b" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Original maximum call, funded by the same actual non-timeout execution,
with exact readonly state/caller binding and one source tick. -/
theorem call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values a b))
    (code : source.code.lookup (ofString "max")=some (formals,body,.one))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "max") expressions continuation)=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (selected a b)) continuation=(result,final) ∧ post=restore source name final := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  let entry := callEntryStateHOLFinite {source with clock:=source.clock+1} callee
  have bodyRun := execute entry a b aLocal bLocal
  obtain ⟨funded,positive,lowered,final,remaining,restored⟩ := terminating_padded_scope_args source post (emptyLocalsHOLFinite entry) name .one (ofString "max") expressions (values a b)
    body continuation callee .one (.val (.word (selected a b))) 1 args called (by decide) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL]) result run notTimeout
  have clock : source.clock+1-1-1=source.clock-1 := by omega
  change evaluateHOLFiniteState (bind {source with clock:=source.clock+1-1-1} name (selected a b)) continuation=(result,final) at remaining
  rw [clock] at remaining
  exact ⟨positive,final,remaining,restored⟩

end InitECandidate.Solver.Input.UnsignedMax

#print axioms InitECandidate.Solver.Input.UnsignedMax.selected_number
#print axioms InitECandidate.Solver.Input.UnsignedMax.execute
#print axioms InitECandidate.Solver.Input.UnsignedMax.original_code
#print axioms InitECandidate.Solver.Input.UnsignedMax.environment
#print axioms InitECandidate.Solver.Input.UnsignedMax.call_trace
