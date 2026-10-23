import InitECandidate.Solver.Mpt.NodeRlpBeginPrepared
import InitECandidate.Solver.Mpt.NodeRlpBeginFooter

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (writeMetadata)

/-- Actual whole begin result. Its three stored frame descriptors and
real heap update are derived; other older words survive unless they are
one of the three literal frame destinations. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (limit : Nat) (value : ValueHOL 64) (allowance : Nat) where
  buffer : BitVec 64
  length : BitVec 64
  payload : BitVec 64
  answer : value=.val (.word 0#64)
  bufferStored : target.memory (frame+24#64)=.word buffer
  lengthStored : target.memory (frame+32#64)=.word length
  payloadStored : target.memory (frame+40#64)=.word payload
  mapped : source.memaddrs (frame+24#64) ∧ source.memaddrs (frame+32#64) ∧ source.memaddrs (frame+40#64)
  branch : wordAt source.memory node=3#64→buffer=0#64 ∧ length=0#64 ∧ payload=0#64
  path : wordAt source.memory node≠3#64→buffer=heap ∧ length.toNat=(wordAt source.memory (node+40#64)).toNat/2+1 ∧
    length.toNat≤payload.toNat ∧ payload.toNat≤(wordAt source.memory (node+40#64)).toNat/2+limit+19 ∧
    heap.toNat+(wordAt source.memory (node+40#64)).toNat/2+2≤33806089496
  fields : writeMetadata target=writeMetadata (preparationBase source node heap)
  older : ∀ query : BitVec 64,query.toNat<heap.toNat→query≠frame+24#64→query≠frame+32#64→query≠frame+40#64→target.memory query=source.memory query
  price : source.clock-target.clock≤allowance

/-- Whole unchanged original257 normal result, including all four outer
declarations, real branch/path preparation, the three actual frame stores
and every lexical restoration. No future helper success is assumed. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    Nonempty (Output source target node heap frame limit value (bodyAllowance source.memory node)) := by
  have price:=body_cost source node heap lower limit property data valueFits installed nodeCell
  rw [normal] at price
  have shaped:=normal
  rw [body_shapes.1] at shaped
  obtain ⟨first,firstRun,firstEnd⟩:=Input.declaration_return_word source target "k" (nodeField 0) (wordAt source.memory node) afterTag value
    (tag_read source node heap lower limit property data nodeCell) shaped
  rw [body_shapes.2.1] at firstRun
  obtain ⟨second,secondRun,secondEnd⟩:=Input.declaration_return_word _ first "payload" (.const 0#64) 0#64 afterPayload value rfl firstRun
  rw [body_shapes.2.2.1] at secondRun
  obtain ⟨third,thirdRun,thirdEnd⟩:=Input.declaration_return_word _ second "cbuf" (.const 0#64) 0#64 afterBuffer value rfl secondRun
  rw [body_shapes.2.2.2.1] at thirdRun
  obtain ⟨fourth,fourthRun,fourthEnd⟩:=Input.declaration_return_word _ third "clen" (.const 0#64) 0#64 afterLength value rfl thirdRun
  let entered:=start source (wordAt source.memory node)
  change evaluateHOLFiniteState entered afterLength=(some (.returned value),fourth) at fourthRun
  rw [body_shapes.2.2.2.2.1] at fourthRun
  have safe:=path_choice_safe (ofString "fr") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨current,preparedRun,footerRun⟩:=Input.sequence_returned entered fourth pathChoice footer value (safe.summary_full entered).2.1 fourthRun
  have cells:=start_cells source (wordAt source.memory node)
  let enteredData:=data.start source node heap (wordAt source.memory node) lower limit property
  obtain ⟨prepared⟩:=path_choice_normal entered current node heap lower limit property enteredData valueFits installed (cells.2.2.2.2.1.trans nodeCell)
    cells.1 cells.2.2.1 cells.2.2.2.1 cells.2.1 preparedRun
  have saved:=safe.summary_full entered
  unfold Input.LocalSummary at saved
  rw [preparedRun] at saved
  have currentFrame : current.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (saved.1 rfl).trans (cells.2.2.2.2.2.trans frameCell)
  obtain ⟨answer,footerEnd,firstMapped,secondMapped,thirdMapped⟩:=footer_normal current fourth frame prepared.buffer prepared.length prepared.payload
    currentFrame prepared.bufferCell prepared.lengthCell prepared.payloadCell value footerRun
  have memory : target.memory=storedMemory current.memory frame prepared.buffer prepared.length prepared.payload:=by
    rw [firstEnd,secondEnd,thirdEnd,fourthEnd,footerEnd]
    rfl
  have finalMetadata : writeMetadata target=writeMetadata current:=by
    rw [firstEnd,secondEnd,thirdEnd,fourthEnd,footerEnd]
    rfl
  have baseMetadata : writeMetadata (preparationBase entered node heap)=writeMetadata (preparationBase source node heap):=by
    have tagEq : wordAt entered.memory node=wordAt source.memory node:=rfl
    by_cases branch : wordAt source.memory node=3#64
    · simp only [preparationBase,tagEq,if_pos branch]
      rfl
    · simp only [preparationBase,tagEq,if_neg branch]
      rfl
  have domain:=congrArg PanSemStateFiniteExact.memaddrs prepared.fields
  change current.memaddrs=(preparationBase entered node heap).memaddrs at domain
  have baseDomain : (preparationBase entered node heap).memaddrs=source.memaddrs:=by
    unfold preparationBase
    split <;> rfl
  have sourceDomain : current.memaddrs=source.memaddrs:=domain.trans baseDomain
  have stored:=stored_fields current.memory frame prepared.buffer prepared.length prepared.payload
  refine ⟨{
    buffer:=prepared.buffer,length:=prepared.length,payload:=prepared.payload,answer:=answer
    bufferStored:=by rw [memory]; exact stored.1
    lengthStored:=by rw [memory]; exact stored.2.1
    payloadStored:=by rw [memory]; exact stored.2.2
    mapped:=by rw [←sourceDomain]; exact ⟨firstMapped,secondMapped,thirdMapped⟩
    branch:=prepared.branch
    path:=prepared.path
    fields:=finalMetadata.trans (prepared.fields.trans baseMetadata)
    older:=by
      intro query older firstAway secondAway thirdAway
      rw [memory,stored_away current.memory frame prepared.buffer prepared.length prepared.payload query firstAway secondAway thirdAway]
      exact prepared.older query older
    price:=price }⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.body_normal
