import InitECandidate.Solver.Input.CurrentRlp.HeaderOptional

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderRest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

theorem budgets : sizes baseRest=816 ∧ costs baseRest=1188:=by decide

theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤50)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source (fields baseRest afterBase)).2.clock≤1291 := by
  have price:=fields_cost source original header buffer baseRest position context installed bounded facts (by rw [budgets.1]; omega)
    p afterBase 103 (by
      intro current finalPosition nextLower nextUpper reached
      have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
      have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
      exact HeaderOptional.cost current original header buffer finalPosition reached.context currentInstalled bounded optional
        (by omega) (by rw [budgets.1] at nextUpper; omega) reached.pointer currentBuf)
  rw [budgets.2] at price
  exact price

theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤50)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source (fields baseRest afterBase)=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_returned source target original header buffer baseRest position
    context installed bounded facts (by rw [budgets.1]; omega) p afterBase value returned
  have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
  have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
  obtain ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩:=HeaderOptional.normal current target original header buffer finalPosition
    reached.context currentInstalled bounded optional (by omega) (by rw [budgets.1] at nextUpper; omega) reached.pointer currentBuf value remaining
  exact ⟨start,encoded,positive,size,answer,arena,metadata.trans reached.metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderRest

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.budgets
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.normal

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderRest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

/-- Only the literal extra-data field uses the finite-domain fallback. -/
theorem current_budgets : currentSizes baseRest=33806090519 ∧ currentPrices baseRest=43314053799 ∧
    ∀ field∈baseRest,FieldWrite.SmallField field := by
  refine ⟨by decide,by decide,?_⟩
  simp [baseRest,FieldWrite.SmallField]

/-- All outcomes of the actual base-field/optional/list suffix sequence.
No parent-record values or read-success facts are supplied. -/
theorem current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (lower : buffer.toNat+9≤position) (upper : position+33806090578<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source (fields baseRest afterBase)).2.clock≤43314053911 := by
  have positiveFloor : 0<buffer.toNat:=by have lower:=reserved.lower; omega
  have price:=fields_current_cost source baseRest heap position buffer.toNat installed domain heapCell heapLower heapBound current_budgets.2.2
    (by rw [current_budgets.1]; omega) p positiveFloor aligned (by omega) beforeHeap afterBase 112 (by
      intro current finalPosition nextLower nextUpper reached
      have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
      have currentDomain : current.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain reached.metadata).trans domain
      have globals:=congrArg PanSemStateFiniteExact.globals reached.metadata
      change current.globals=source.globals at globals
      have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
      have currentBuf:=(reached.locals (ofString "buf") (by decide) (by decide)).trans buf
      exact HeaderOptional.current_cost current buffer heap finalPosition currentInstalled currentDomain currentHeap heapLower heapBound reserved aligned beforeHeap
        (by omega) (by rw [current_budgets.1] at nextUpper; omega) reached.pointer currentBuf)
  rw [current_budgets.2.1] at price
  exact price

/-- A genuine returned base sequence derives its bounded actual output end
and retains the full older physical input prefix for the next hash. -/
theorem current_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (lower : buffer.toNat+9≤position) (upper : position+33806090578<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (fields baseRest afterBase)=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤position+33806090569-buffer.toNat ∧ buffer.toNat≤start.toNat ∧
      start.toNat≤buffer.toNat+8 ∧ position≤start.toNat+encoded ∧ start.toNat+encoded≤position+33806090569 ∧ value=encodedPair start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query) := by
  have positiveFloor : 0<buffer.toNat:=by have lower:=reserved.lower; omega
  obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_current_returned source target baseRest heap position buffer.toNat
    installed domain heapCell heapLower heapBound current_budgets.2.2 (by rw [current_budgets.1]; omega) p positiveFloor aligned
    (by omega) beforeHeap afterBase value normal
  rw [current_budgets.1] at nextUpper
  have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
  have currentDomain : current.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain reached.metadata).trans domain
  have globals:=congrArg PanSemStateFiniteExact.globals reached.metadata
  change current.globals=source.globals at globals
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  have currentBuf:=(reached.locals (ofString "buf") (by decide) (by decide)).trans buf
  obtain ⟨start,encoded,positive,size,startLower,startUpper,endLower,endUpper,answer,metadata,memory⟩:=HeaderOptional.current_normal current target buffer heap finalPosition
    currentInstalled currentDomain currentHeap heapLower heapBound reserved aligned beforeHeap (by omega) (by omega) reached.pointer currentBuf value remaining
  refine ⟨start,encoded,positive,by omega,startLower,startUpper,by omega,by omega,answer,metadata.trans reached.metadata,?_⟩
  intro query before
  exact (memory query before).trans (reached.memory query before)

end InitECandidate.Solver.Input.CurrentRlp.HeaderRest

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.current_budgets
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.current_normal
