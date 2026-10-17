import InitECandidate.Solver.Input.HeaderEncoding.Whole

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (header : BitVec 64)
    (lookup : codeFn (ofString "encode_header")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "encode_header") [.val (.word header)]=some (body,callee,returnShape) ∧
      callee.lookup (ofString "h")=some (.val (.word header)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word header)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word header)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "encode_header") [.val (.word header)]=
      some (body,CallNormal.unaryLocals "h" header,returnShape) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [CallNormal.unaryLocals]

def callerPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (memory : Memory)
    (name : String) (start : BitVec 64) (encoded paid : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  setVarHOLFinite (ofString name) (encodedPair start encoded) (post source buffer memory paid)

/-- Real pair-valued header call, with its heap advance, memory effects,
caller local restoration and explicit source-clock allowance. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word header)])
    (code : source.code.lookup (ofString "encode_header")=some (formals,body,returnShape))
    (geometry : Geometry header buffer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer)))
    (codes : Codes source) (tailCodes : TailCodes source)
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (facts : ∀ field∈firstField::baseRest,FieldFacts source.memory header field)
    (optionalFacts : wordAt source.memory (address header 0)≠0#64→∀ field∈optionalFields,FieldFacts source.memory header field)
    (enough : 1346≤source.clock) :
    ∃ memory start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤1346 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "encode_header") expressions continuation)=
        (let output:=evaluateHOLFiniteState (callerPost source buffer memory name start encoded paid) continuation
        (output.1,restore source name output.2)) ∧ OldMemory memory source.memory buffer := by
  obtain ⟨callee,called,h⟩:=environment source.code.lookup header code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,start,encoded,paid,positive,sizeBound,bound,number,run,frame,memoryFrame⟩:=execute entry header buffer geometry domain h heap
    (Codes.of_code source entry rfl codes) (TailCodes.of_code source entry rfl tailCodes) allocCode facts optionalFacts
    (by change 1345≤source.clock-1; omega)
  have actual:=CallNormal.return_execute source target name returnShape (ofString "encode_header") expressions [.val (.word header)] body continuation callee returnShape
    (encodedPair start encoded) args called (by omega) run (by simp [encodedPair,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
  have canonical : CallNormal.continuationEntry source target name (encodedPair start encoded)=callerPost source buffer target.memory name start encoded (paid+1) := by
    change setVarHOLFinite (ofString name) (encodedPair start encoded) {target with locals:=source.locals}=_
    change {target with locals:=source.locals}={source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (cursor buffer)))
      memory:=target.memory
      clock:=source.clock-1-paid} at callerFrame
    rw [subtract] at callerFrame
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) (encodedPair start encoded) state) callerFrame
  refine ⟨target.memory,start,encoded,paid+1,positive,sizeBound,by omega,number,?_,memoryFrame⟩
  rw [canonical] at actual
  exact actual

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.environment
#print axioms InitECandidate.Solver.Input.HeaderEncoding.call_execute
