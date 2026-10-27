import InitECandidate.Solver.Input.Requests.Program
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.Input.NonTimeoutScopedCall
import InitECandidate.Solver.Input.SszGuardTrace

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def afterGuard : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip

theorem guard_shape : body = .seq shortGuard afterGuard := by
  simp only [afterGuard,body_shape]

theorem length_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (present : source.locals.lookup (ofString "len") = some (.val (.word length))) :
    QueryBranch.eval source shortTest = some (.val (.word (if length.toNat < 20 then 1#64 else 0#64))) := by
  simp [QueryBranch.eval,shortTest,QueryBranch.localVar,evalHOLExact,toExact,present,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

def values (pointer length : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word length)]
def rawLocals (pointer length : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "len" then some (.val (.word length)) else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer length : BitVec 64)
    (lookup : codeFn (ofString "decode_requests")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "decode_requests") (values pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "decode_requests") (values pointer length)=some (body,rawLocals pointer length,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "len" from by decide]
  · simp [rawLocals]

/-- Real request caller and minimum-length guard on every actual enclosing
non-timeout execution. Short slices raise the original SszErr60 within two
caller/body ticks; passing reaches the actual remaining callee body. -/
theorem call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values pointer length))
    (code : source.code.lookup (ofString "decode_requests") = some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString "rq") .one (ofString "decode_requests") arguments continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (length.toNat < 20 ∧ result = some (.exception (ofString "SszErr") (.val (.word 60#64))) ∧ source.clock - post.clock ≤ 2) ∨
    (20 ≤ length.toNat ∧ ∃ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (bodyResult : Option (PanSemResultExact 64)) (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
      lookupCodeHOLFinite source.code.lookup (ofString "decode_requests") (values pointer length) = some (body,callee,.one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧ callee.lookup (ofString "len") = some (.val (.word length)) ∧
      1 ≤ source.clock ∧ bodyResult ≠ some .timeOut ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) afterGuard = (bodyResult,bodyPost)) := by
  obtain ⟨callee,called,p,n⟩ := environment source.code.lookup pointer length code
  obtain ⟨funded,bodyNotTimeout⟩ := scoped_call_non_timeout source post (ofString "rq") .one (ofString "decode_requests") arguments (values pointer length)
    body continuation callee .one args called result run notTimeout
  let entry := callEntryStateHOLFinite source callee
  change (evaluateHOLFiniteState entry body).1 ≠ some .timeOut at bodyNotTimeout
  generalize computed : evaluateHOLFiniteState entry body = output at bodyNotTimeout
  obtain ⟨bodyResult,bodyPost⟩ := output
  have guardRun : evaluateHOLFiniteState entry (.seq shortGuard afterGuard) = (bodyResult,bodyPost) := by rw [← guard_shape]; exact computed
  have test := length_test_read entry length n
  rcases Header.guard_trace entry bodyPost shortTest 60#64 (length.toNat < 20) afterGuard test failCode shape bodyResult guardRun bodyNotTimeout with short | valid
  · obtain ⟨tooShort,_,same,endpoint⟩ := short
    have actualBody : evaluateHOLFiniteState entry body = (some (.exception (ofString "SszErr") (.val (.word 60#64))),bodyPost) := by rw [computed,same]
    have actual := run
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at actual
    simp only [args,called,if_neg (show source.clock ≠ 0 by omega)] at actual
    rw [actualBody] at actual
    have resultEq := congrArg Prod.fst actual
    have endpointClock := congrArg (fun output => output.2.clock) actual
    change some (PanSemResultExact.exception (ofString "SszErr") (.val (.word 60#64))) = result at resultEq
    change bodyPost.clock = post.clock at endpointClock
    have bodyClock : bodyPost.clock = source.clock - 1 - 1 := by rw [endpoint]; rfl
    exact Or.inl ⟨tooShort,resultEq.symm,by rw [← endpointClock,bodyClock]; omega⟩
  · exact Or.inr ⟨by omega,callee,bodyResult,bodyPost,called,p,n,funded,bodyNotTimeout,valid.2⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.guard_shape
#print axioms InitECandidate.Solver.Input.Requests.length_test_read
#print axioms InitECandidate.Solver.Input.Requests.environment
#print axioms InitECandidate.Solver.Input.Requests.call_trace
