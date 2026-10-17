import InitECandidate.Solver.GasBudget.Minimum

namespace InitECandidate.Solver.GasBudget.AddExact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_add_sat with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",.one),(ofString "b",.one)]
def sumExpression : ExpHOL 64 := .op .add [localVar "a",localVar "b"]
def tail : ProgHOL 64 := .seq (.ite (.cmp .lower (localVar "s") (localVar "a"))
  (.return (.const 18446744073709551615#64)) .skip) (.return (localVar "s"))

theorem body_shape : body=.dec (ofString "s") .one sumExpression tail := by
  simp only [body,Guest.guestFn_add_sat,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,sumExpression,tail,localVar]

/-- The actual saturating helper takes its exact-add branch whenever the
natural sum fits. This premise is supplied by the gas-pool invariant. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (fits : a.toNat+b.toNat<2^64) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word (a+b)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  have sumRead : eval source sumExpression=some (.val (.word (a+b))) := by
    simp [eval,sumExpression,evalHOLExact,evalListHOLExact,toExact,localVar,aLocal,bLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  let entered:=bind source "s" (a+b)
  have aE : entered.locals.lookup (ofString "a")=some (.val (.word a)):=
    (bind_lookup_other _ "s" "a" _ (by decide)).trans aLocal
  have sE : entered.locals.lookup (ofString "s")=some (.val (.word (a+b))):=bind_lookup_same _ _ _
  have notOverflow : ¬a+b<a := by
    change ¬(a+b).toNat<a.toNat
    rw [BitVec.toNat_add_of_lt fits]
    omega
  have tailRun : evaluateHOLFiniteState entered tail=(some (.returned (.val (.word (a+b)))),emptyLocalsHOLFinite entered) := by
    simp [tail,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,
      evalHOLExact,toExact,localVar,aE,sE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,notOverflow,shapeOfHOLExact,sizeOfShapeWithContextHOL,fixClockHOLFinite]
  refine ⟨restore source "s" (emptyLocalsHOLFinite entered),?_,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "s" sumExpression (a+b) tail _ sumRead tailRun

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : BitVec 64)
    (lookup : codeFn (ofString "add_sat")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "add_sat") [.val (.word a),.val (.word b)]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "b")=some (.val (.word b)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word a),.val (.word b)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word a),.val (.word b)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "add_sat") [.val (.word a),.val (.word b)]=some (body,Minimum.rawLocals a b,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [Minimum.rawLocals,show ofString "a"≠ofString "b" from by decide]
  · simp [Minimum.rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word a),.val (.word b)])
    (code : source.code.lookup (ofString "add_sat")=some (formals,body,.one)) (fits : a.toNat+b.toNat<2^64) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "add_sat") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (a+b)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,frame⟩:=execute entry a b aLocal bLocal fits
  have actual:=Input.CallNormal.pure_return_execute source target name (ofString "add_sat") expressions [.val (.word a),.val (.word b)]
    body continuation callee (a+b) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.GasBudget.AddExact

#print axioms InitECandidate.Solver.GasBudget.AddExact.body_shape
#print axioms InitECandidate.Solver.GasBudget.AddExact.execute
#print axioms InitECandidate.Solver.GasBudget.AddExact.environment
#print axioms InitECandidate.Solver.GasBudget.AddExact.call_execute
