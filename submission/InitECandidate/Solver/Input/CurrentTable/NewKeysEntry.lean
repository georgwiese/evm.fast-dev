import InitECandidate.Solver.Input.CurrentTable.NewPrefix
import InitECandidate.Solver.Input.CurrentTable.NewStores

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def keysEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) :=
  headerStored (fieldsEntry source heap cap) heap cap

/-- Literal lexical bindings after the real first allocation and both
current declarations. None is reconstructed from a later successful call. -/
theorem fields_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) :
    (fieldsEntry source heap cap).locals.lookup (ofString "t")=some (.val (.word heap)) ∧
    (fieldsEntry source heap cap).locals.lookup (ofString "key_len")=some (.val (.word 32#64)) ∧
    (fieldsEntry source heap cap).locals.lookup (ofString "stride")=some (.val (.word 32#64)) ∧
    (fieldsEntry source heap cap).locals.lookup (ofString "cap")=some (.val (.word cap)) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (bind_lookup_other (strideEntry source heap) "ncap" "t" cap (by decide)).trans
      ((bind_lookup_other (tableEntry source heap) "stride" "t" 32#64 (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other (strideEntry source heap) "ncap" "key_len" cap (by decide)).trans
      ((bind_lookup_other (tableEntry source heap) "stride" "key_len" 32#64 (by decide)).trans
      ((bind_lookup_other _ "t" "key_len" heap (by decide)).trans keyLocal))
  · exact (bind_lookup_other (strideEntry source heap) "ncap" "stride" cap (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other (strideEntry source heap) "ncap" "cap" cap (by decide)).trans
      ((bind_lookup_other (tableEntry source heap) "stride" "cap" 32#64 (by decide)).trans
      ((bind_lookup_other _ "t" "cap" heap (by decide)).trans capLocal))

/-- The real next constructor caller has its advanced heap, unchanged
clock apart from the one allocation call and protected earlier memory. -/
theorem keys_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (arena : AllocatedBytes.Arena heap 88) :
    (keysEntry source heap cap).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 88#64))) ∧
    (keysEntry source heap cap).clock=source.clock-1 ∧
    (∀ query : BitVec 64,query.toNat<heap.toNat→(keysEntry source heap cap).memory query=source.memory query) ∧
    (∀ key : MlS,key≠ofString "heap_ptr"→(keysEntry source heap cap).globals.lookup key=source.globals.lookup key) := by
  refine ⟨?_,rfl,?_,?_⟩
  · simp [keysEntry,headerStored,putField,fieldsEntry,strideEntry,tableEntry,WitnessRadix.QueryBranch.bind,
      setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · intro query before
    exact header_before (fieldsEntry source heap cap) heap cap query arena before
  · intro key different
    simp [keysEntry,headerStored,putField,fieldsEntry,strideEntry,tableEntry,WitnessRadix.QueryBranch.bind,
      setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm different]

/-- A complete current constructor prefix through the initial metadata
stores either stops within two source ticks or reaches the real keys-array
allocation with derived fresh-header room and exact scope restoration. -/
theorem keys_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨
      1≤source.clock ∧ heap.toNat+88≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      ∃ inner,evaluateHOLFiniteState (keysEntry source heap cap) keysCall=(outcome,inner) ∧ post=restorePrefix source heap inner := by
  rcases entry_trace source post heap cap keyLocal capLocal atLeastTwo heapCell heapLower heapBound heapAligned installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨funded,room,arena,inner,continued,endpoint⟩:=reached
    obtain ⟨tableCell,keyCell,strideCell,capCell⟩:=fields_cells source heap cap keyLocal capLocal
    rw [fields_execute (fieldsEntry source heap cap) heap cap domain arena heapAligned tableCell keyCell strideCell capCell] at continued
    exact Or.inr ⟨funded,room,arena,inner,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.fields_cells
#print axioms InitECandidate.Solver.Input.CurrentTable.New.keys_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.New.keys_trace
