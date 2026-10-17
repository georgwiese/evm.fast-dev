import InitECandidate.Solver.Input.RlpLength.BlockCall

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def sizeTest : ExpHOL 64 := .cmp .lower (.const 8388608#64) (localVar "bl")
def sizeGuard : ProgHOL 64 := .ite sizeTest (.raise (ofString "BlockErr") (.const 7#64)) .skip
def payloadBody : ProgHOL 64 := match Guest.guestFn_payload_header with | .function fn=>progToHOL fn.body | _=>.skip
def lengthContinuations : ProgHOL 64→List (ProgHOL 64)
  | .decCall _ _ function _ rest=>(if function=ofString "block_rlp_length" then [rest] else [])++lengthContinuations rest
  | .dec _ _ _ rest | .while _ rest=>lengthContinuations rest
  | .seq first second | .ite _ first second=>lengthContinuations first++lengthContinuations second
  | _=>[]
def payloadAfterLength : ProgHOL 64 := ((lengthContinuations payloadBody)[0]?).getD .skip

theorem size_guard_subtree : (match payloadAfterLength with | .seq first _=>first | _=>.skip)=sizeGuard := by
  simp only [payloadAfterLength,payloadBody,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,lengthContinuations]
  simp only [show ofString "alloc"≠ofString "block_rlp_length" from by decide,
    show ofString "encode_withdrawal_rlp"≠ofString "block_rlp_length" from by decide,
    show ofString "encode_execution_requests"≠ofString "block_rlp_length" from by decide,
    if_false,if_true,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some]
  rfl

theorem size_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (encoded : Nat)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded)
    (exceptionShape : source.eshapes.lookup (ofString "BlockErr")=some .one) :
    evaluateHOLFiniteState source sizeGuard=
      if encoded≤8388608 then (none,source)
      else (some (.exception (ofString "BlockErr") (.val (.word 7#64))),emptyLocalsHOLFinite source) := by
  classical
  have testRead : eval source sizeTest=some (.val (.word (if 8388608<encoded then 1#64 else 0#64))) := by
    have comparison : 8388608#64<BitVec.ofNat 64 encoded↔8388608<encoded := by
      change (8388608#64).toNat<(BitVec.ofNat 64 encoded).toNat↔8388608<encoded
      rw [number]
      rfl
    simp [eval,sizeTest,localVar,evalHOLExact,toExact,bl,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison]
  simp only [eval] at testRead
  rw [sizeGuard,evaluateHOLFiniteState_ite,testRead]
  by_cases small : encoded≤8388608
  · simp [small,show ¬8388608<encoded from by omega]
  · simp [small,show 8388608<encoded from by omega,evaluateHOLFiniteState_raise,exceptionShape,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- Passing the actual payload_header guard after the computed block length
enforces the withdrawal cap. Oversized blocks stop before the continuation. -/
theorem count_of_guarded_continuation (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count encoded : Nat)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (minimum : 25*count≤encoded)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded)
    (exceptionShape : source.eshapes.lookup (ofString "BlockErr")=some .one)
    (normal : evaluateHOLFiniteState source (.seq sizeGuard continuation)=(some (.returned value),post)) : count≤335544 := by
  by_contra outside
  have big : ¬encoded≤8388608 := by omega
  have guardRun:=size_guard_execute source encoded bl number exceptionShape
  rw [if_neg big] at guardRun
  have stopped:=WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) sizeGuard continuation
    (.exception (ofString "BlockErr") (.val (.word 7#64))) guardRun (Nat.le_refl _)
  rw [stopped] at normal
  cases normal

/-- Combine the actual whole block call with its literal payload guard. Every
successful continuation has the cap; the encoded header is computed here. -/
theorem guarded_call_count (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (value : ValueHOL 64)
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
    (exceptionShape : source.eshapes.lookup (ofString "BlockErr")=some .one)
    (enough : 12*VarList.decodedCount input txStart txLength+43*wdCount+1382≤source.clock)
    (normal : evaluateHOLFiniteState source (.decCall (ofString "bl") .one (ofString "block_rlp_length") expressions (.seq sizeGuard continuation))=
      (some (.returned value),post)) : wdCount≤335544 := by
  obtain ⟨memory,encoded,paid,lower,upper,bound,number,callRun,memoryFrame⟩:=call_execute source input pointer array payload header buffer txStart txLength wdStart wdCount
    "bl" expressions (.seq sizeGuard continuation) args code domain data geometry inputBefore arrayBefore cellsBefore heap codes facts optionalFacts enough
  rw [callRun] at normal
  let entered:=bind {source with memory:=memory,clock:=source.clock-paid} "bl" (BitVec.ofNat 64 encoded)
  have result:=congrArg Prod.fst normal
  change (evaluateHOLFiniteState entered (.seq sizeGuard continuation)).1=some (.returned value) at result
  have enteredNormal : evaluateHOLFiniteState entered (.seq sizeGuard continuation)=
      (some (.returned value),(evaluateHOLFiniteState entered (.seq sizeGuard continuation)).2) := Prod.ext result rfl
  exact count_of_guarded_continuation entered _ wdCount encoded continuation value lower (bind_lookup_same _ _ _) number exceptionShape enteredNormal

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.size_guard_subtree
#print axioms InitECandidate.Solver.Input.RlpLength.Block.size_guard_execute
#print axioms InitECandidate.Solver.Input.RlpLength.Block.count_of_guarded_continuation
#print axioms InitECandidate.Solver.Input.RlpLength.Block.guarded_call_count
