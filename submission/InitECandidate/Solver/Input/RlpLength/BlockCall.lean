import InitECandidate.Solver.Input.RlpLength.WholeBlock

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rawLocals (header payload : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "pl" then some (.val (.word payload)) else if name=ofString "hdr" then some (.val (.word header)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (header payload : BitVec 64)
    (lookup : codeFn (ofString "block_rlp_length")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "block_rlp_length") [.val (.word header),.val (.word payload)]=some (body,callee,.one) ∧
      callee.lookup (ofString "hdr")=some (.val (.word header)) ∧ callee.lookup (ofString "pl")=some (.val (.word payload)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word header),.val (.word payload)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word header),.val (.word payload)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "block_rlp_length") [.val (.word header),.val (.word payload)]=some (body,rawLocals header payload,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "hdr"≠ofString "pl" from by decide]
  · simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word header),.val (.word payload)])
    (code : source.code.lookup (ofString "block_rlp_length")=some (formals,body,.one))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer)))
    (codes : Codes source)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optionalFacts : HeaderEncoding.wordAt source.memory (HeaderEncoding.address header 0)≠0#64→
      ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (enough : 12*VarList.decodedCount input txStart txLength+43*wdCount+1382≤source.clock) :
    ∃ memory encoded paid,25*wdCount≤encoded ∧ encoded≤436208508+57*wdCount ∧
      paid≤12*VarList.decodedCount input txStart txLength+43*wdCount+1382 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "block_rlp_length") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with memory:=memory,clock:=source.clock-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2)) ∧ HeaderEncoding.OldMemory memory source.memory buffer := by
  obtain ⟨callee,called,h,p⟩:=environment source.code.lookup header payload code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame,memoryFrame⟩:=execute entry input pointer array payload header buffer txStart txLength wdStart wdCount
    domain (Data.of_fields source entry input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data) geometry inputBefore arrayBefore cellsBefore h p heap
    (Codes.of_code source entry rfl codes) facts optionalFacts (by change 12*VarList.decodedCount input txStart txLength+43*wdCount+1381≤source.clock-1; omega)
  have actual:=CallNormal.memory_return_execute source target name (ofString "block_rlp_length") expressions [.val (.word header),.val (.word payload)] body continuation callee
    (BitVec.ofNat 64 encoded) paid args called (by omega) run frame
  have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
  refine ⟨target.memory,encoded,paid+1,lower,upper,by omega,number,?_,memoryFrame⟩
  simpa only [subtract] using actual

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.environment
#print axioms InitECandidate.Solver.Input.RlpLength.Block.call_execute
