import InitECandidate.Solver.Input.RlpWrite.U256MinBuilt

namespace InitECandidate.Solver.Input.RlpWrite.U256Min
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  byteCode : source.code.lookup (ofString "u256_byte_length")=some (U256ByteLength.formals,U256ByteLength.body,.one)
  bitsCode : source.code.lookup (ofString "u256_bit_length")=some (U256Bits.formals,U256Bits.body,.one)
  bitCode : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)
  limbCode : source.code.lookup (ofString "u256_limb")=some (U256Limb.formals,U256Limb.body,.one)

def rawLocals (words : U256Value.Words) (dst : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word dst)) else if name=ofString "a" then some (U256Value.tuple words) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (words : U256Value.Words) (dst : BitVec 64)
    (lookup : codeFn (ofString "u256_to_be_min")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "u256_to_be_min") [U256Value.tuple words,.val (.word dst)]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (U256Value.tuple words) ∧ callee.lookup (ofString "out")=some (.val (.word dst)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([U256Value.tuple words,.val (.word dst)] : List (ValueHOL 64)).length ∧
      ((formals.zip [U256Value.tuple words,.val (.word dst)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_to_be_min") [U256Value.tuple words,.val (.word dst)]=some (body,rawLocals words dst,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a"≠ofString "out" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [U256Value.tuple words,.val (.word dst)])
    (code : source.code.lookup (ofString "u256_to_be_min")=some (formals,body,.one)) (codes : Codes source)
    (mapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))) (enough : 68≤source.clock) :
    ∃ memory length paid,length≤32 ∧ paid≤67 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_to_be_min") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-1-paid} name (BitVec.ofNat 64 length)) continuation
        (output.1,restore source name output.2)) ∧
      (∀ query,(∀ offset<32,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))→memory query=source.memory query) := by
  obtain ⟨callee,called,a,outLocal⟩:=environment source.code.lookup words dst code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,length,paid,bound,paidBound,bodyRun,frame,memory⟩:=execute entry words dst a outLocal codes.byteCode codes.bitsCode codes.bitCode codes.limbCode mapped
    (by change 67≤source.clock-1; omega)
  exact ⟨target.memory,length,paid,bound,paidBound,
    CallNormal.memory_return_execute source target name (ofString "u256_to_be_min") expressions [U256Value.tuple words,.val (.word dst)]
      body continuation callee (BitVec.ofNat 64 length) paid args called (by omega) bodyRun frame,memory⟩

end InitECandidate.Solver.Input.RlpWrite.U256Min

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.environment
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.call_execute
