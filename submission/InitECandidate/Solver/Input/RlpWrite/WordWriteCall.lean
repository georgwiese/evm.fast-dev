import InitECandidate.Solver.Input.RlpWrite.WordWrite
import InitECandidate.Solver.Input.MemoryReturn

namespace InitECandidate.Solver.Input.RlpWrite.WordWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rawLocals (dst w : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "w" then some (.val (.word w)) else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst w : BitVec 64)
    (lookup : codeFn (ofString "rlp_encode_word")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "rlp_encode_word") [.val (.word dst),.val (.word w)]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "w")=some (.val (.word w)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),.val (.word w)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),.val (.word w)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_encode_word") [.val (.word dst),.val (.word w)]=some (body,rawLocals dst w,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "w" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst w : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),.val (.word w)])
    (code : source.code.lookup (ofString "rlp_encode_word")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 19≤source.clock) :
    ∃ memory encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_encode_word") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2)) ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,v⟩:=environment source.code.lookup dst w code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame,memory⟩:=execute entry dst w d v beCode putCode mapped (by change 18≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,upper,bound,
    CallNormal.memory_return_execute source target name (ofString "rlp_encode_word") expressions [.val (.word dst),.val (.word w)] body continuation callee
      (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame,memory⟩

theorem assign_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst w old : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64))
    (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),.val (.word w)])
    (code : source.code.lookup (ofString "rlp_encode_word")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 19≤source.clock) :
    ∃ memory encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "rlp_encode_word") expressions)=
        (none,bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,v⟩:=environment source.code.lookup dst w code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame,memory⟩:=execute entry dst w d v beCode putCode mapped (by change 18≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,upper,bound,
    CallNormal.memory_assign_execute source target name old (ofString "rlp_encode_word") expressions [.val (.word dst),.val (.word w)] body callee
      (BitVec.ofNat 64 encoded) paid present args called (by omega) bodyRun frame,memory⟩

end InitECandidate.Solver.Input.RlpWrite.WordWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.call_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.assign_execute
