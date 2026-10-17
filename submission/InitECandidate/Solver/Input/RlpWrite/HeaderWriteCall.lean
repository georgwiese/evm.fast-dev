import InitECandidate.Solver.Input.RlpWrite.HeaderWrite
import InitECandidate.Solver.Input.MemoryReturn

namespace InitECandidate.Solver.Input.RlpWrite.HeaderWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rawLocals (dst base n : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word n)) else if name=ofString "base" then some (.val (.word base))
  else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst base n : BitVec 64)
    (lookup : codeFn (ofString "rlp_write_header")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "rlp_write_header") [.val (.word dst),.val (.word base),.val (.word n)]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "base")=some (.val (.word base)) ∧
      callee.lookup (ofString "n")=some (.val (.word n)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),.val (.word base),.val (.word n)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),.val (.word base),.val (.word n)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_write_header") [.val (.word dst),.val (.word base),.val (.word n)]=some (body,rawLocals dst base n,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "n" from by decide,show ofString "dst"≠ofString "base" from by decide]
  · simp [rawLocals,show ofString "base"≠ofString "n" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst base n : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),.val (.word base),.val (.word n)])
    (code : source.code.lookup (ofString "rlp_write_header")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 19≤source.clock) :
    ∃ memory encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_write_header") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2)) ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,b,len⟩:=environment source.code.lookup dst base n code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame,memory⟩:=execute entry dst base n d b len beCode putCode mapped (by change 18≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,upper,bound,
    CallNormal.memory_return_execute source target name (ofString "rlp_write_header") expressions [.val (.word dst),.val (.word base),.val (.word n)] body continuation callee
      (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame,memory⟩

theorem tail_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst base n : BitVec 64) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),.val (.word base),.val (.word n)])
    (code : source.code.lookup (ofString "rlp_write_header")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 19≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source (.call none (ofString "rlp_write_header") expressions)=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-paid} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  obtain ⟨callee,called,d,b,len⟩:=environment source.code.lookup dst base n code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame,memory⟩:=execute entry dst base n d b len beCode putCode mapped (by change 18≤source.clock-1; omega)
  have actual:=evaluateHOLFiniteState_call_return_none source (.val (.word (BitVec.ofNat 64 encoded))) (ofString "rlp_write_header") expressions
    [.val (.word dst),.val (.word base),.val (.word n)] body callee .one target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have outerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-paid}:=frame
  exact ⟨emptyLocalsHOLFinite target,encoded,paid,lower,upper,bound,actual,by simpa only [emptyLocalsHOLFinite] using outerFrame,memory⟩

end InitECandidate.Solver.Input.RlpWrite.HeaderWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.call_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.tail_call_execute
