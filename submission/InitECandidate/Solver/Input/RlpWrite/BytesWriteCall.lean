import InitECandidate.Solver.Input.RlpWrite.BytesWriteBuilt

namespace InitECandidate.Solver.Input.RlpWrite.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Access (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (byte : UInt8) : Prop where
  small : length≤134217712
  loaded : length=1→ @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be src=some byte
  headerMapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))
  copyMapped : ∀ header,1≤header→header≤9→WitnessRadix.CopyContext.Mapped source src (dst+BitVec.ofNat 64 header) length

structure Codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  header : source.code.lookup (ofString "rlp_write_header")=some (HeaderWrite.formals,HeaderWrite.body,.one)
  beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one)
  put : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one)
  copyCode : source.code.lookup (ofString "memcpy")=some (WitnessRadix.CopyGeneral.formals,WitnessRadix.Copy32.body,.one)

def rawLocals (dst src n : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word n)) else if name=ofString "src" then some (.val (.word src))
  else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst src n : BitVec 64)
    (lookup : codeFn (ofString "rlp_encode_bytes")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "rlp_encode_bytes") [.val (.word dst),.val (.word src),.val (.word n)]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "src")=some (.val (.word src)) ∧
      callee.lookup (ofString "n")=some (.val (.word n)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),.val (.word src),.val (.word n)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),.val (.word src),.val (.word n)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_encode_bytes") [.val (.word dst),.val (.word src),.val (.word n)]=some (body,rawLocals dst src n,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "n" from by decide,show ofString "dst"≠ofString "src" from by decide]
  · simp [rawLocals,show ofString "src"≠ofString "n" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (byte : UInt8)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))])
    (code : source.code.lookup (ofString "rlp_encode_bytes")=some (formals,body,.one))
    (access : Access source dst src length byte) (codes : Codes source) (enough : length+21≤source.clock) :
    ∃ memory encoded paid,length≤encoded ∧ 1≤encoded ∧ encoded≤length+9 ∧ paid≤length+20 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_encode_bytes") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2)) ∧ (∀ query,Away dst query (length+9)→memory query=source.memory query) := by
  obtain ⟨callee,called,d,s,n⟩:=environment source.code.lookup dst src (BitVec.ofNat 64 length) code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,positive,upper,bound,number,bodyRun,frame,memory⟩:=execute entry dst src length byte access.small d s n access.loaded
    codes.header codes.beCode codes.put codes.copyCode access.headerMapped
      (by intro header lower upper; exact WitnessRadix.CopyContext.Mapped.of_domain source entry _ _ _ rfl (access.copyMapped header lower upper))
      (by change length+20≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,positive,upper,bound,number,
    CallNormal.memory_return_execute source target name (ofString "rlp_encode_bytes") expressions [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))]
      body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame,memory⟩

theorem assign_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src old : BitVec 64) (length : Nat) (byte : UInt8)
    (name : String) (expressions : List (ExpHOL 64)) (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))])
    (code : source.code.lookup (ofString "rlp_encode_bytes")=some (formals,body,.one))
    (access : Access source dst src length byte) (codes : Codes source) (enough : length+21≤source.clock) :
    ∃ memory encoded paid,length≤encoded ∧ 1≤encoded ∧ encoded≤length+9 ∧ paid≤length+20 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "rlp_encode_bytes") expressions)=
        (none,bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) ∧
      (∀ query,Away dst query (length+9)→memory query=source.memory query) := by
  obtain ⟨callee,called,d,s,n⟩:=environment source.code.lookup dst src (BitVec.ofNat 64 length) code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,positive,upper,bound,number,bodyRun,frame,memory⟩:=execute entry dst src length byte access.small d s n access.loaded
    codes.header codes.beCode codes.put codes.copyCode access.headerMapped
      (by intro header lower upper; exact WitnessRadix.CopyContext.Mapped.of_domain source entry _ _ _ rfl (access.copyMapped header lower upper))
      (by change length+20≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,positive,upper,bound,number,
    CallNormal.memory_assign_execute source target name old (ofString "rlp_encode_bytes") expressions [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))]
      body callee (BitVec.ofNat 64 encoded) paid present args called (by omega) bodyRun frame,memory⟩

end InitECandidate.Solver.Input.RlpWrite.BytesWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.call_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.assign_execute
