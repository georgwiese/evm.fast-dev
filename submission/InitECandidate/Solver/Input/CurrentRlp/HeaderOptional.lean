import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

theorem optional_append (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tail : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq optionalCode tail)=evaluateHOLFiniteState source (fields optionalFields tail) := by
  simp only [optionalCode,optionalFields,fields,evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState source (call (.bytes 232 32))=first
  obtain ⟨firstResult,firstPost⟩:=first
  cases firstResult with
  | some result=>rfl
  | none=>
    generalize evaluateHOLFiniteState firstPost advance=second
    obtain ⟨secondResult,secondPost⟩:=second
    cases secondResult with
    | some result=>rfl
    | none=>
      generalize evaluateHOLFiniteState secondPost (call (.scalar 240))=third
      obtain ⟨thirdResult,thirdPost⟩:=third
      cases thirdResult <;> rfl

/-- The current-header flag is read from the actual retained header cell. -/
theorem choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) :
    evaluateHOLFiniteState source afterBase=
      if wordAt original (address header 0)=0#64 then evaluateHOLFiniteState source suffix
      else evaluateHOLFiniteState source (fields optionalFields suffix) := by
  have read:=context.load_one source original header buffer 0 (by decide) (by decide)
  have testRead : eval source currentTest=some (.val (.word (if wordAt original (address header 0)=0#64 then 0#64 else 1#64))):=by
    simp only [eval] at read ⊢
    rw [currentTest,evalHOLExact,read]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at testRead
  by_cases zero : wordAt original (address header 0)=0#64
  · rw [if_pos zero,afterBase,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,testRead]
    simp [zero,evaluateHOLFiniteState_skip]
  · rw [if_neg zero]
    rw [←optional_append source suffix]
    simp only [afterBase,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,testRead,if_neg zero]
    rfl

/-- The real optional branch and final list header cost at most103source
clock ticks on every outcome, after the actual base fields. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016) (facts : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤866)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source afterBase).2.clock≤103 := by
  rw [choice source original header buffer context]
  split
  · have price:=HeaderSuffix.cost source original header buffer position context installed lower (by omega) p buf
    omega
  · have priced:=fields_cost source original header buffer optionalFields position context installed bounded facts
      (by change position+50≤1024; omega) p suffix 31 (by
        intro current finalPosition nextLower nextUpper reached
        have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
        have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
        exact HeaderSuffix.cost current original header buffer finalPosition reached.context currentInstalled (by omega)
          (by change finalPosition≤position+50 at nextUpper; omega) reached.pointer currentBuf)
    change source.clock-(evaluateHOLFiniteState source (fields optionalFields suffix)).2.clock≤72+31 at priced
    exact priced

/-- An actual returning optional branch supplies the same mapped final
encoding and protected older memory as the genuine suffix. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016) (facts : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤866)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source afterBase=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  rw [choice source original header buffer context] at returned
  split at returned
  · exact HeaderSuffix.normal source target original header buffer position context installed lower (by omega) p buf value returned
  · obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_returned source target original header buffer optionalFields position
      context installed bounded facts (by change position+50≤1024; omega) p suffix value returned
    have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
    have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
    obtain ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩:=HeaderSuffix.normal current target original header buffer finalPosition
      reached.context currentInstalled (by omega) (by change finalPosition≤position+50 at nextUpper; omega) reached.pointer currentBuf value remaining
    exact ⟨start,encoded,positive,size,answer,arena,metadata.trans reached.metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderOptional

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.optional_append
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.choice
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.normal

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

/-- Distribute the actual suffix over the real flag decision. Failed or
ill-typed reads still stop with the same state and outcome. -/
theorem current_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evaluateHOLFiniteState source afterBase=evaluateHOLFiniteState source (.ite currentTest (fields optionalFields suffix) suffix) := by
  rw [afterBase,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_ite]
  generalize read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun query=>Classical.propDecidable (source.memaddrs query)) currentTest=observed
  cases observed with
  | none=>rfl
  | some observed=>
    cases observed with
    | rStruct fields=>rfl
    | nStruct name fields=>rfl
    | val payload=>
      cases payload with
      | word word=>
        by_cases zero : word=0
        · simp [zero,evaluateHOLFiniteState_skip]
        · simp only [if_neg zero]
          simpa only [evaluateHOLFiniteState_seq_line780] using optional_append source suffix

private theorem current_branch (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.ite currentTest (fields optionalFields suffix) suffix)=(some (.returned value),target)) :
    evaluateHOLFiniteState source (fields optionalFields suffix)=(some (.returned value),target) ∨
      evaluateHOLFiniteState source suffix=(some (.returned value),target) := by
  rw [evaluateHOLFiniteState_ite] at normal
  generalize read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun query=>Classical.propDecidable (source.memaddrs query)) currentTest=observed at normal
  cases observed with
  | none=>cases normal
  | some observed=>
    cases observed with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero] at normal; exact Or.inr normal
        · rw [if_neg zero] at normal; exact Or.inl normal

theorem current_budgets : currentSizes optionalFields=50 ∧ currentPrices optionalFields=81 ∧
    ∀ field∈optionalFields,FieldWrite.SmallField field := by
  refine ⟨by decide,by decide,?_⟩
  intro field member
  simp [optionalFields] at member
  rcases member with rfl|rfl <;> unfold FieldWrite.SmallField <;> decide

/-- All actual flag/optional-field/list-header outcomes, with no decoded
header-image premise. The flag read itself may fail or have the wrong shape. -/
theorem current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (lower : buffer.toNat+9≤position) (upper : position+59<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source afterBase).2.clock≤112 := by
  have positiveFloor : 0<buffer.toNat:=by have lower:=reserved.lower; omega
  have optionalPrice:=fields_current_cost source optionalFields heap position buffer.toNat installed domain heapCell heapLower heapBound
    current_budgets.2.2 (by rw [current_budgets.1]; omega) p positiveFloor aligned (by omega) beforeHeap suffix 31 (by
      intro current finalPosition nextLower nextUpper reached
      have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
      have currentDomain : current.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain reached.metadata).trans domain
      have currentBuf:=(reached.locals (ofString "buf") (by decide) (by decide)).trans buf
      exact HeaderSuffix.current_cost current buffer finalPosition currentInstalled currentDomain reserved aligned (by omega)
        (by rw [current_budgets.1] at nextUpper; omega) reached.pointer currentBuf)
  rw [current_budgets.2.1] at optionalPrice
  have suffixPrice:=HeaderSuffix.current_cost source buffer position installed domain reserved aligned lower (by omega) p buf
  rw [current_choice]
  exact ClockCost.conditional_current source currentTest (fields optionalFields suffix) suffix 112 31 optionalPrice suffixPrice

/-- The actual optional branch derives the real final span and its output
end, bounded by the fixed optional bytes, and preserves the earlier input. -/
theorem current_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (lower : buffer.toNat+9≤position) (upper : position+59<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterBase=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤position+50-buffer.toNat ∧ buffer.toNat≤start.toNat ∧
      start.toNat≤buffer.toNat+8 ∧ position≤start.toNat+encoded ∧ start.toNat+encoded≤position+50 ∧ value=encodedPair start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query) := by
  rw [current_choice] at normal
  rcases current_branch source target value normal with optional|skipped
  · have positiveFloor : 0<buffer.toNat:=by have lower:=reserved.lower; omega
    obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_current_returned source target optionalFields heap position buffer.toNat
      installed domain heapCell heapLower heapBound current_budgets.2.2 (by rw [current_budgets.1]; omega) p positiveFloor aligned
      (by omega) beforeHeap suffix value optional
    rw [current_budgets.1] at nextUpper
    have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
    have currentDomain : current.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain reached.metadata).trans domain
    have currentBuf:=(reached.locals (ofString "buf") (by decide) (by decide)).trans buf
    obtain ⟨start,encoded,positive,size,startLower,startUpper,endNumber,answer,metadata,memory⟩:=HeaderSuffix.current_normal current target buffer finalPosition
      currentInstalled currentDomain reserved aligned (by omega) (by omega) reached.pointer currentBuf value remaining
    refine ⟨start,encoded,positive,by omega,startLower,startUpper,by omega,by omega,answer,metadata.trans reached.metadata,?_⟩
    intro query before
    exact (memory query before).trans (reached.memory query before)
  · obtain ⟨start,encoded,positive,size,startLower,startUpper,endNumber,answer,metadata,memory⟩:=HeaderSuffix.current_normal source target buffer position
      installed domain reserved aligned lower (by omega) p buf value skipped
    exact ⟨start,encoded,positive,by omega,startLower,startUpper,by omega,by omega,answer,metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderOptional

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.current_choice
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.current_budgets
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.current_normal
