import InitECandidate.Solver.Input.RequestProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := Scalar.payloadBody
def lengthTest : ExpHOL 64 := .cmp .lower (localVar "len") (.const 540#64)
def lengthGuard : ProgHOL 64 := .ite lengthTest (.call (some (none,none)) (ofString "ssz_fail") [.const 50#64]) .skip
def afterGuard : ProgHOL 64 := match body with | .seq _ rest=>rest | _=>.skip

theorem body_shape : body=.seq lengthGuard afterGuard := by
  simp only [body,Scalar.payloadBody,afterGuard,Guest.guestFn_decode_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,lengthGuard,lengthTest,localVar]

theorem length_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (present : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    eval source lengthTest=some (.val (.word (if length.toNat<540 then 1#64 else 0#64))) := by
  classical
  simp [eval,lengthTest,localVar,evalHOLExact,toExact,present,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- Actual payload length rejection or exact entry to the remaining fixed body.
Rejected slices raise SszErr50 and cannot resume the decoder. -/
theorem entry_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (present : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source body=
      if length.toNat<540 then (some (.exception (ofString "SszErr") (.val (.word 50#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else evaluateHOLFiniteState source afterGuard := by
  have test:=length_test_read source length present
  have guarded:=Header.test_guard_execute source lengthTest 50#64 (length.toNat<540) test failCode exceptionShape enough
  rw [body_shape]
  by_cases short : length.toNat<540
  · simp only [if_pos short] at guarded ⊢
    exact WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ guarded (by change source.clock-1≤source.clock; omega)
  · simp only [if_neg short] at guarded ⊢
    exact WitnessRadix.StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _)

def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "len",.one)]
def values (pointer length : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word length)]
def rawLocals (pointer length : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "len" then some (.val (.word length)) else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer length : BitVec 64)
    (lookup : codeFn (ofString "decode_payload")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "decode_payload") (values pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "decode_payload") (values pointer length)=some (body,rawLocals pointer length,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "len" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.body_shape
#print axioms InitECandidate.Solver.Input.Payload.length_test_read
#print axioms InitECandidate.Solver.Input.Payload.entry_execute
#print axioms InitECandidate.Solver.Input.Payload.environment
