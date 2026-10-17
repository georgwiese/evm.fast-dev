import InitECandidate.Solver.Input.RlpWrite.U256PutBuilt

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rawLocals (dst : BitVec 64) (words : U256Value.Words) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "v" then some (U256Value.tuple words) else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst : BitVec 64) (words : U256Value.Words)
    (lookup : codeFn (ofString "rlp_put_u256")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "rlp_put_u256") [.val (.word dst),U256Value.tuple words]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "v")=some (U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),U256Value.tuple words] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),U256Value.tuple words]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_put_u256") [.val (.word dst),U256Value.tuple words]=some (body,rawLocals dst words,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "v" from by decide]
  · simp [rawLocals]

theorem Codes.of_code (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (same : target.code=source.code) (codes : Codes source) : Codes target := by
  constructor
  · rw [same]; exact codes.markCode
  · rw [same]; exact codes.allocCode
  · rw [same]; exact codes.minCode
  · constructor
    · rw [same]; exact codes.minCodes.byteCode
    · rw [same]; exact codes.minCodes.bitsCode
    · rw [same]; exact codes.minCodes.bitCode
    · rw [same]; exact codes.minCodes.limbCode
  · rw [same]; exact codes.bytesCode
  · constructor
    · rw [same]; exact codes.bytesCodes.header
    · rw [same]; exact codes.bytesCodes.beCode
    · rw [same]; exact codes.bytesCodes.put
    · rw [same]; exact codes.bytesCodes.copyCode
  · rw [same]; exact codes.releaseCode

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst cursor : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),U256Value.tuple words])
    (code : source.code.lookup (ofString "rlp_put_u256")=some (formals,body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (codes : Codes source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cursorLower : 2701131776≤cursor.toNat) (fits : cursor.toNat+32≤33806089496)
    (dstArena : WitnessRadix.AllocatedBytes.Arena dst 41) (enough : 125≤source.clock) :
    ∃ memory encoded paid,1≤encoded ∧ encoded≤41 ∧ paid≤124 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_put_u256") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2)) ∧
      (∀ query,BytesWrite.Away dst query 41→(∀ offset<32,query≠panByteAlignHOL (width:=64) (cursor+BitVec.ofNat 64 offset))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,v⟩:=environment source.code.lookup dst words code
  let entry:=callEntryStateHOLFinite source callee
  have entryCodes:=Codes.of_code source entry rfl codes
  obtain ⟨target,encoded,paid,lower,upper,bound,number,bodyRun,frame,memory⟩:=execute entry words dst cursor v d heap entryCodes domain cursorLower fits dstArena (by change 124≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,upper,bound,number,
    CallNormal.memory_return_execute source target name (ofString "rlp_put_u256") expressions [.val (.word dst),U256Value.tuple words]
      body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame,memory⟩

theorem assign_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst cursor old : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word dst),U256Value.tuple words])
    (code : source.code.lookup (ofString "rlp_put_u256")=some (formals,body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (codes : Codes source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cursorLower : 2701131776≤cursor.toNat) (fits : cursor.toNat+32≤33806089496)
    (dstArena : WitnessRadix.AllocatedBytes.Arena dst 41) (enough : 125≤source.clock) :
    ∃ memory encoded paid,1≤encoded ∧ encoded≤41 ∧ paid≤124 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "rlp_put_u256") expressions)=
        (none,bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) ∧
      (∀ query,BytesWrite.Away dst query 41→(∀ offset<32,query≠panByteAlignHOL (width:=64) (cursor+BitVec.ofNat 64 offset))→memory query=source.memory query) := by
  obtain ⟨callee,called,d,v⟩:=environment source.code.lookup dst words code
  let entry:=callEntryStateHOLFinite source callee
  have entryCodes:=Codes.of_code source entry rfl codes
  obtain ⟨target,encoded,paid,lower,upper,bound,number,bodyRun,frame,memory⟩:=execute entry words dst cursor v d heap entryCodes domain cursorLower fits dstArena (by change 124≤source.clock-1; omega)
  exact ⟨target.memory,encoded,paid,lower,upper,bound,number,
    CallNormal.memory_assign_execute source target name old (ofString "rlp_put_u256") expressions [.val (.word dst),U256Value.tuple words]
      body callee (BitVec.ofNat 64 encoded) paid present args called (by omega) bodyRun frame,memory⟩

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.Codes.of_code
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.call_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.assign_execute
