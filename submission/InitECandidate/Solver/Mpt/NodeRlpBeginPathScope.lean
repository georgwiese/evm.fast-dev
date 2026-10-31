import InitECandidate.Solver.Mpt.NodeRlpBeginCost

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame)

theorem path_scope_safe (key : MlS) (notPath : key≠ofString "nlen") (notBuffer : key≠ofString "cbuf") (notFlag : key≠ofString "isl")
    (notLength : key≠ofString "clen") (notPayload : key≠ofString "payload") (notEncoded : key≠ofString "el") (notValue : key≠ofString "vl") :
    Input.LocalPrefix key pathScope := by
  rw [path_shapes.1,path_shapes.2.1]
  exact .dec _ _ _ notPath (.seq (.call (some (ofString "cbuf")) _ _ (by intro name same; cases same; exact notBuffer))
    (after_allocation_safe key notFlag notLength notPayload notEncoded notValue))

theorem path_choice_safe (key : MlS) (notPath : key≠ofString "nlen") (notBuffer : key≠ofString "cbuf") (notFlag : key≠ofString "isl")
    (notLength : key≠ofString "clen") (notPayload : key≠ofString "payload") (notEncoded : key≠ofString "el") (notValue : key≠ofString "vl") :
    Input.LocalPrefix key pathChoice := by
  rw [body_shapes.2.2.2.2.2]
  exact .ite _ (path_scope_safe key notPath notBuffer notFlag notLength notPayload notEncoded notValue) .skip

/-- Actual original nlen scope: all operand facts follow from current
registered-node ownership. Normal execution derives the allocated buffer,
true sizes, updated heap frame and preservation of every older word. -/
theorem path_scope_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap oldBuffer : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word oldBuffer)))
    (normal : evaluateHOLFiniteState source pathScope=(none,target)) :
    let pathLength:=wordAt source.memory (node+40#64)
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19) ∧
      target.locals.lookup (ofString "cbuf")=some (.val (.word heap)) ∧
      heap.toNat+pathLength.toNat/2+2≤2952790016 ∧
      SpanFrame (PersistentAlloc.post source heap (allocationAmount pathLength)) target heap (pathLength.toNat/2+1) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query) := by
  dsimp only
  let pathLength:=wordAt source.memory (node+40#64)
  rw [path_shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "nlen" (nodeField 40) pathLength afterPathLength
    (path_size_read source node heap lower limit property data pathTag nodeCell) normal
  obtain ⟨⟨length,payload,lengthCell,size,payloadCell,payloadLower,payloadUpper⟩,buffer,room,frame,older⟩:=after_path_length_normal _ inner node (wordAt source.memory node) pathLength limit property
    (path_input source node heap oldBuffer lower limit property data pathTag nodeCell tagCell bufferCell)
    (by have :=pathLength.isLt; omega) installed continued
  refine ⟨⟨length,payload,?_,size,?_,payloadLower,payloadUpper⟩,?_,room,?_,?_⟩
  · rw [endpoint,restore_lookup_other source inner "nlen" "clen" (by decide)]
    exact lengthCell
  · rw [endpoint,restore_lookup_other source inner "nlen" "payload" (by decide)]
    exact payloadCell
  · rw [endpoint,restore_lookup_other source inner "nlen" "cbuf" (by decide)]
    exact buffer
  · rw [endpoint]
    exact ⟨frame.fields,frame.memory⟩
  · rw [endpoint]
    exact older

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_scope_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_choice_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_scope_normal
