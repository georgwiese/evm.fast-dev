import InitECandidate.Solver.Input.RlpWrite.U256Value

namespace InitECandidate.Solver.Input.RlpWrite.U256Limb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_u256_limb with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",U256Value.tupleShape),(ofString "i",.one)]
def test (index : Fin 4) : ExpHOL 64 := .cmp .equal (localVar "i") (.const (BitVec.ofNat 64 index.val))
def scan : List (Fin 4)→ProgHOL 64
  | []=>.return (.const 0#64)
  | index::rest=>.seq (.ite (test index) (.return (U256Value.limb index)) .skip) (scan rest)

theorem body_shape : body=scan [0,1,2,3] := by
  simp only [body,Guest.guestFn_u256_limb,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,scan,test,U256Value.limb,localVar]
  rfl

theorem scan_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (value : BitVec 64) (indices : List (Fin 4))
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (i : source.locals.lookup (ofString "i")=some (.val (.word value))) :
    ∃ word,evaluateHOLFiniteState source (scan indices)=(some (.returned (.val (.word word))),emptyLocalsHOLFinite source) := by
  classical
  induction indices with
  | nil=>
    refine ⟨0#64,?_⟩
    simp [scan,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | cons index rest ih=>
    have readTest : eval source (test index)=some (.val (.word (if value=BitVec.ofNat 64 index.val then 1#64 else 0#64))) := by
      simp [eval,test,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at readTest
    by_cases equal : value=BitVec.ofNat 64 index.val
    · have read:=U256Value.limb_read source words index a
      simp only [eval] at read
      have returned : evaluateHOLFiniteState source (.return (U256Value.limb index))=
          (some (.returned (.val (.word (words index)))),emptyLocalsHOLFinite source) := by
        rw [evaluateHOLFiniteState_return,read]
        simp [shapeOfHOLExact,sizeOfShapeWithContextHOL]
      have guardRun : evaluateHOLFiniteState source (.ite (test index) (.return (U256Value.limb index)) .skip)=
          (some (.returned (.val (.word (words index)))),emptyLocalsHOLFinite source) := by
        rw [evaluateHOLFiniteState_ite,readTest]
        simpa [equal] using returned
      refine ⟨words index,?_⟩
      rw [scan]
      exact WitnessRadix.StateSteps.stopped_sequence source _ _ _ (.returned (.val (.word (words index)))) guardRun (Nat.le_refl _)
    · have guardRun : evaluateHOLFiniteState source (.ite (test index) (.return (U256Value.limb index)) .skip)=(none,source) := by
        rw [evaluateHOLFiniteState_ite,readTest]
        simp [equal]
      obtain ⟨word,run⟩:=ih
      refine ⟨word,?_⟩
      rw [scan,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
      exact run

def rawLocals (words : U256Value.Words) (index : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "i" then some (.val (.word index)) else if name=ofString "a" then some (U256Value.tuple words) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (words : U256Value.Words) (index : BitVec 64)
    (lookup : codeFn (ofString "u256_limb")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "u256_limb") [U256Value.tuple words,.val (.word index)]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (U256Value.tuple words) ∧ callee.lookup (ofString "i")=some (.val (.word index)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([U256Value.tuple words,.val (.word index)] : List (ValueHOL 64)).length ∧
      ((formals.zip [U256Value.tuple words,.val (.word index)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_limb") [U256Value.tuple words,.val (.word index)]=some (body,rawLocals words index,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a"≠ofString "i" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (index : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [U256Value.tuple words,.val (.word index)])
    (code : source.code.lookup (ofString "u256_limb")=some (formals,body,.one)) (enough : 1≤source.clock) :
    ∃ word,evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_limb") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name word) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,a,i⟩:=environment source.code.lookup words index code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨word,run⟩:=scan_execute entry words index [0,1,2,3] a i
  have bodyRun : evaluateHOLFiniteState entry body=(some (.returned (.val (.word word))),emptyLocalsHOLFinite entry) := by rw [body_shape]; exact run
  have frame : emptyLocalsHOLFinite (emptyLocalsHOLFinite entry)=emptyLocalsHOLFinite {source with clock:=source.clock-1-0}:=rfl
  have actual:=CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "u256_limb") expressions [U256Value.tuple words,.val (.word index)]
    body continuation callee word 0 args called enough bodyRun frame
  exact ⟨word,by simpa only [Nat.sub_zero] using actual⟩

end InitECandidate.Solver.Input.RlpWrite.U256Limb

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Limb.scan_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Limb.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Limb.call_execute
