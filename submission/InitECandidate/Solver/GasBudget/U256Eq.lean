import InitECandidate.Solver.GasBudget.U256Zero

namespace InitECandidate.Solver.GasBudget.U256Eq
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
abbrev Quad:=U256Zero.Quad
def body : ProgHOL 64:=match Guest.guestFn_u256_eq with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "a",Input.RlpWrite.U256Value.tupleShape),(ofString "b",Input.RlpWrite.U256Value.tupleShape)]
def mixed (a b : Quad) : BitVec 64:=U256Zero.mixed (fun i=>a i ^^^ b i)
noncomputable def resultWord (a b : Quad) : BitVec 64:=by
  classical
  exact if a=b then 1#64 else 0#64

theorem mixed_zero (a b : Quad) : mixed a b=0#64 ↔ a=b := by
  rw [mixed,U256Zero.mixed_zero]
  simp only [BitVec.xor_eq_zero_iff,funext_iff]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple b)) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (resultWord a b)))),emptyLocalsHOLFinite source) := by
  classical
  have xorFold : ∀ x y : BitVec 64,XorOp.xor x (XorOp.xor y 0#64)=x ^^^ y := by
    intro x y
    change x ^^^ (y ^^^ 0#64)=x ^^^ y
    simp
  have folded : OrOp.or (a 0 ^^^ b 0) (OrOp.or (a 1 ^^^ b 1) (OrOp.or (a 2 ^^^ b 2) (OrOp.or (a 3 ^^^ b 3) 0#64)))=mixed a b := by
    change (a 0 ^^^ b 0) ||| ((a 1 ^^^ b 1) ||| ((a 2 ^^^ b 2) ||| ((a 3 ^^^ b 3) ||| 0#64)))=mixed a b
    simp [mixed,U256Zero.mixed]
  have zeros : OrOp.or (0#64) (OrOp.or (0#64) (OrOp.or (0#64) (OrOp.or 0#64 0#64)))=0#64:=by decide
  by_cases same : a=b
  · have zero : mixed a b=0#64:=(mixed_zero a b).mpr same
    simp [body,Guest.guestFn_u256_eq,progToHOL,expToHOL,resultWord,evaluateHOLFiniteState_seq,
      evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
      valueIsWord,valueWord,wordOpHOL,wordOp,xorFold,folded,zeros,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same,zero,shapeOfHOLExact,
      fixClockHOLFinite,emptyLocalsHOLFinite]
  · have nonzero : mixed a b≠0#64:=fun eq=>same ((mixed_zero a b).mp eq)
    simp [body,Guest.guestFn_u256_eq,progToHOL,expToHOL,resultWord,evaluateHOLFiniteState_seq,
      evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
      valueIsWord,valueWord,wordOpHOL,wordOp,xorFold,folded,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same,nonzero,shapeOfHOLExact,
      fixClockHOLFinite,emptyLocalsHOLFinite]

def rawLocals (a b : Quad) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "b" then some (Input.RlpWrite.U256Value.tuple b)
  else if name=ofString "a" then some (Input.RlpWrite.U256Value.tuple a) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : Quad)
    (lookup : codeFn (ofString "u256_eq")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "u256_eq") [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple a) ∧
      callee.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple b) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] : List (ValueHOL 64)).length ∧
      ((formals.zip [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "a"≠ofString "b" from by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_eq") [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]=some (body,rawLocals a b,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a"≠ofString "b" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b])
    (code : source.code.lookup (ofString "u256_eq")=some (formals,body,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_eq") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (resultWord a b)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b code
  let entry:=callEntryStateHOLFinite source callee
  have run:=execute entry a b aLocal bLocal
  have actual:=Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "u256_eq") expressions _
    body continuation callee (resultWord a b) 0 args called enough run rfl
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.GasBudget.U256Eq

#print axioms InitECandidate.Solver.GasBudget.U256Eq.mixed_zero
#print axioms InitECandidate.Solver.GasBudget.U256Eq.execute
#print axioms InitECandidate.Solver.GasBudget.U256Eq.environment
#print axioms InitECandidate.Solver.GasBudget.U256Eq.call_execute


namespace InitECandidate.Solver.GasBudget.U256Eq
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem current_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_eq")=some (formals,body,.one) := by
  have known:=ArithmeticEffects.current_environment code installed .u256_eq
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    body,formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_eq,shapeToHOL,List.map_cons,List.map_nil] using known

end InitECandidate.Solver.GasBudget.U256Eq

#print axioms InitECandidate.Solver.GasBudget.U256Eq.current_code
