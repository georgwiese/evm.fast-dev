import InitECandidate.Solver.Mpt.IndexedInitialModel
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Genuine whole-builder normal execution reaches its real root/hash
footer with the completed live map, saved release mark, original output
binding and older caller band. No later footer execution is invented. -/
theorem normal_after_updates (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap array : BitVec 64)
    (count limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (heapLower : 2713731432≤heap.toNat)
    (countBound : count<2^64) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (installed : Input.OriginalCode.Installed source.code) (bindings : Input.Main.MptWorkspace.Bindings source)
    (hash : Keccak256.Environment source 2713714976#64 2713715176#64)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (rows : SliceArray source array count heap.toNat limit slices property) (empty : property 0#64 0#64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ (current inner : PanSemStateFiniteExact 64 Guest.HostMemory) (model : LoopModel current heap array count heap.toNat limit slices property),
      model.index.toNat=count ∧ heap.toNat≤model.heap.toNat ∧
      current.locals.lookup (ofString "mark")=some (.val (.word heap)) ∧
      current.locals.lookup (ofString "out")=source.locals.lookup (ofString "out") ∧
      (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<heap.toNat→current.memory query=source.memory query) ∧
      target.clock=inner.clock ∧ evaluateHOLFiniteState current afterLoop=(some (.returned value),inner) := by
  obtain ⟨inner,initial,_index,clock,continued⟩:=normal_loop_entry source target heap array count limit slices property heapCell frontier aligned heapLower countBound domain little installed bindings hash scratch rows empty countCell arrayCell value normal
  have safe : Input.LocalPrefix (ofString "n") (.while test loopBody):=.loop test loop_body_limit
  rw [loop_shape] at continued
  obtain ⟨current,loopRun,footerRun⟩:=Input.sequence_returned (loopEntry source heap) inner (.while test loopBody) afterLoop value
    (fun returned=>(safe.summary_full (loopEntry source heap)).2.1 returned) continued
  obtain ⟨model,finished,grows,memory⟩:=loop_normal (loopEntry source heap) current heap array count heap.toNat limit slices property initial loopRun
  have saved (name : MlS) (notKey : name≠ofString "klen") (notIndex : name≠ofString "i") :
      current.locals.lookup name=(loopEntry source heap).locals.lookup name:=by
    have summary:=(Input.LocalPrefix.loop test (loop_body_saved name notKey notIndex)).summary_full (loopEntry source heap)
    unfold Input.LocalSummary at summary
    rw [loopRun] at summary
    exact summary.1 rfl
  have markCell : (loopEntry source heap).locals.lookup (ofString "mark")=some (.val (.word heap)):=by
    simp [loopEntry,newEntry,marked,Input.CallPrefix.heapMarked,NewTrie.post,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  exact ⟨current,inner,model,finished,initial.floor.trans grows,(saved (ofString "mark") (by decide) (by decide)).trans markCell,
    (saved (ofString "out") (by decide) (by decide)).trans (loop_entry_saved source heap (ofString "out") (by decide) (by decide) (by decide)),
    (by
      intro query above before
      exact (memory query above before).trans (loop_entry_older source heap query initial.header.arena before)),clock,footerRun⟩

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.normal_after_updates
