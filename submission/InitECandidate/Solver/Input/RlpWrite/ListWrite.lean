import InitECandidate.Solver.Input.RlpWrite.HeaderWriteCall

namespace InitECandidate.Solver.Input.RlpWrite.ListWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_encode_list_header with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "payload_len",.one)]
def arguments : List (ExpHOL 64) := [localVar "dst",.const 192#64,localVar "payload_len"]

theorem body_shape : body=.call none (ofString "rlp_write_header") arguments := by
  simp only [body,Guest.guestFn_rlp_encode_list_header,progToHOL,expToHOL,List.map_cons,List.map_nil,arguments,localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst payload : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "payload_len")=some (.val (.word payload)))
    (headerCode : source.code.lookup (ofString "rlp_write_header")=some (HeaderWrite.formals,HeaderWrite.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 19≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤19 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word 192#64),.val (.word payload)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  obtain ⟨target,encoded,paid,lower,upper,bound,run,frame,memory⟩:=HeaderWrite.tail_call_execute source dst 192#64 payload arguments args headerCode beCode putCode mapped enough
  refine ⟨target,encoded,paid+1,lower,upper,by omega,?_,?_,memory⟩
  · rw [body_shape]
    exact run
  · have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
    simpa only [subtract] using frame

def rawLocals (dst payload : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "payload_len" then some (.val (.word payload)) else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst payload : BitVec 64)
    (lookup : codeFn (ofString "rlp_encode_list_header")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "rlp_encode_list_header") [.val (.word dst),.val (.word payload)]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "payload_len")=some (.val (.word payload)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),.val (.word payload)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),.val (.word payload)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_encode_list_header") [.val (.word dst),.val (.word payload)]=some (body,rawLocals dst payload,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "payload_len" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst payload : BitVec 64) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),.val (.word payload)])
    (code : source.code.lookup (ofString "rlp_encode_list_header")=some (formals,body,.one))
    (headerCode : source.code.lookup (ofString "rlp_write_header")=some (HeaderWrite.formals,HeaderWrite.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 20≤source.clock) :
    ∃ memory paid,paid≤19 ∧ evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_list_header") expressions)=
      (none,{source with memory:=memory,clock:=source.clock-1-paid}) ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,n⟩:=environment source.code.lookup dst payload code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame,memory⟩:=execute entry dst payload d n headerCode beCode putCode mapped (by change 19≤source.clock-1; omega)
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "rlp_encode_list_header") expressions [.val (.word dst),.val (.word payload)] body callee .one
    (.val (.word (BitVec.ofNat 64 encoded))) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  refine ⟨target.memory,paid,bound,?_,memory⟩
  exact actual.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,state)) callerFrame)

end InitECandidate.Solver.Input.RlpWrite.ListWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.ListWrite.execute
#print axioms InitECandidate.Solver.Input.RlpWrite.ListWrite.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.ListWrite.call_execute
