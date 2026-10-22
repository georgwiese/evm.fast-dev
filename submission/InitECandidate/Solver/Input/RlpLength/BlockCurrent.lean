import InitECandidate.Solver.Input.RlpLength.WholeBlock
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def price (input : Guest.InputBlob) (start length withdrawals : Nat):=
  12*VarList.decodedCount input start length+43*withdrawals+1381

/-- The same physical/data premises bound every evaluator outcome,
including short-clock executions, without an entry clock allowance. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (codes : Codes source)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optionalFacts : HeaderEncoding.wordAt source.memory (HeaderEncoding.address header 0)≠0#64→
      ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤price input txStart txLength wdCount := by
  by_cases enough : price input txStart txLength wdCount≤source.clock
  · obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame,old⟩:=execute source input pointer array payload header buffer
      txStart txLength wdStart wdCount domain data geometry inputBefore arrayBefore cellsBefore hdr pl heap codes facts optionalFacts enough
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤_
    unfold price
    omega
  · omega

/-- Invert a true normal return using clock padding. The actual returned
length, restored heap/metadata, input preservation and bounded cost are
derived even when the initial clock is below the conservative allowance. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (codes : Codes source)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optionalFacts : HeaderEncoding.wordAt source.memory (HeaderEncoding.address header 0)≠0#64→
      ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,25*wdCount≤encoded ∧ encoded≤436208508+57*wdCount ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤price input txStart txLength wdCount ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=target.clock} ∧
      HeaderEncoding.OldMemory target.memory source.memory buffer := by
  let padding:=price input txStart txLength wdCount
  let padded:={source with clock:=source.clock+padding}
  have paddedData:=Data.of_fields source padded input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data
  obtain ⟨post,encoded,paid,lower,upper,bound,number,run,frame,old⟩:=execute padded input pointer array payload header buffer
    txStart txLength wdStart wdCount domain paddedData geometry inputBefore arrayBefore cellsBefore hdr pl heap
    (Codes.of_code source padded rfl codes) facts optionalFacts (by change padding≤source.clock+padding; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target padding
    ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have returned:=congrArg Prod.fst same
  have postEq:=congrArg Prod.snd same
  change {target with clock:=target.clock+padding}=post at postEq
  have cost:=body_cost source input pointer array payload header buffer txStart txLength wdStart wdCount domain data geometry
    inputBefore arrayBefore cellsBefore hdr pl heap codes facts optionalFacts
  rw [normal] at cost
  rw [←postEq] at frame old
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=target.clock}) frame
  change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=target.clock} at restored
  have valueEq : value=.val (.word (BitVec.ofNat 64 encoded)):=by
    change (some (PanSemResultExact.returned value) : Option (PanSemResultExact 64))=
      some (PanSemResultExact.returned (.val (.word (BitVec.ofNat 64 encoded)))) at returned
    exact PanSemResultExact.returned.inj (Option.some.inj returned)
  exact ⟨encoded,lower,upper,number,valueEq,cost,restored,old⟩

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.body_cost
#print axioms InitECandidate.Solver.Input.RlpLength.Block.body_normal
