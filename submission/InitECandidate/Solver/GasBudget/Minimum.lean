import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.GasBudget.Minimum
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_min with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",.one),(ofString "b",.one)]
def selected (a b : BitVec 64) : BitVec 64 := if a<b then a else b

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (selected a b)))),emptyLocalsHOLFinite source) := by
  classical
  by_cases less : a<b
  all_goals simp [body,Guest.guestFn_min,progToHOL,expToHOL,List.map_cons,List.map_nil,selected,
    evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,toExact,
    aLocal,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,less,shapeOfHOLExact,sizeOfShapeWithContextHOL,fixClockHOLFinite,emptyLocalsHOLFinite]

theorem selected_number (a b : BitVec 64) : (selected a b).toNat=min a.toNat b.toNat := by
  by_cases less : a<b
  · simp only [selected,if_pos less,Nat.min_eq_left (Nat.le_of_lt (show a.toNat<b.toNat from less))]
  · simp only [selected,if_neg less,Nat.min_eq_right (show b.toNat≤a.toNat from by change ¬a.toNat<b.toNat at less; omega)]

def rawLocals (a b : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "b" then some (.val (.word b)) else if name=ofString "a" then some (.val (.word a)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : BitVec 64)
    (lookup : codeFn (ofString "min")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "min") [.val (.word a),.val (.word b)]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "b")=some (.val (.word b)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word a),.val (.word b)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word a),.val (.word b)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "min") [.val (.word a),.val (.word b)]=some (body,rawLocals a b,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a"≠ofString "b" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word a),.val (.word b)])
    (code : source.code.lookup (ofString "min")=some (formals,body,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "min") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (selected a b)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b code
  let entry:=callEntryStateHOLFinite source callee
  have run:=execute entry a b aLocal bLocal
  have actual:=Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "min") expressions [.val (.word a),.val (.word b)]
    body continuation callee (selected a b) 0 args called enough run rfl
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.GasBudget.Minimum

#print axioms InitECandidate.Solver.GasBudget.Minimum.execute
#print axioms InitECandidate.Solver.GasBudget.Minimum.selected_number
#print axioms InitECandidate.Solver.GasBudget.Minimum.environment
#print axioms InitECandidate.Solver.GasBudget.Minimum.call_execute
