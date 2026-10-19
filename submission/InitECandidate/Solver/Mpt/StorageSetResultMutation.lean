import InitECandidate.Solver.Mpt.StorageSetResultControl

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

/-- Compose a reached account-cache prefix with the real storage suffix.
Its actual clocks, unchanged journal counter, full word frame and family
potential supply every cross-phase obligation. -/
theorem Result.prepend_mutation {ι : Type} [Fintype ι]
    {source ready post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor readyCursor cutoff population base cap count : Nat} {objects middle : ι → TableFamily.Object} {outer : ι}
    {accounts : List (BitVec 64)} {property : ι → BitVec 64 → Prop} {budget : Bool → Nat}
    (result : Result ready post readyCursor cutoff population middle outer base cap count accounts property budget)
    (prefixPaid prefixPrice : Nat) (fundedPrefix : prefixPaid ≤ source.clock)
    (prefixBound : prefixPaid + TableFamily.potential objects ≤ prefixPrice + TableFamily.potential middle)
    (readyClock : ready.clock = source.clock - prefixPaid) (forwardPrefix : cursor ≤ readyCursor)
    (prefixFrame : TableFamily.PersistentFrame cutoff cursor objects middle source ready)
    (prefixMetadata : TableFamily.Metadata objects middle) (prefixGlobals : HeapGlobals source ready) (readyCode : ready.code = source.code) :
    Result source post cursor cutoff population objects outer base cap count accounts property (fun created => prefixPrice + budget created) := by
  obtain ⟨κ,finite,embed,next,nextProperty,paid,nextCursor,added,created,nextEntries,injective,card,funded,clock,forward,appends,room,models,image,zone,price,populations,codes,
    environment,globals,values,saved,registry,effect,frame,metadata,counter,propertyEmbed,propertyOthers,references⟩ := result
  rw [readyClock] at funded clock
  have totalFunded : prefixPaid + paid ≤ source.clock := by
    calc
      _ ≤ prefixPaid + (source.clock - prefixPaid) := Nat.add_le_add_left funded _
      _ = source.clock := Nat.add_sub_of_le fundedPrefix
  have totalClock : post.clock = source.clock - (prefixPaid + paid) := by rw [clock,Nat.sub_sub]
  have totalGlobals : Journal.OtherGlobals source post := by
    intro name notHeap notCounter
    exact (globals name notHeap notCounter).trans (prefixGlobals name notHeap)
  have prefixEffect := Journal.CounterEffect.unchanged source ready (prefixGlobals (Flapjack.Basis.Pure.MlString.ofString "journal_n") (by decide))
  have totalEffect : Journal.CounterEffect source post added 0 0 := by
    simpa only [Nat.zero_add,Nat.add_zero] using prefixEffect.trans effect
  refine ⟨κ,finite,embed,next,nextProperty,prefixPaid + paid,nextCursor,added,created,nextEntries,injective,card,totalFunded,totalClock,by omega,appends,room,models,image,zone,
    by dsimp only; omega,populations,codes.trans readyCode,environment,totalGlobals,values,saved,registry,totalEffect,?_,?_,counter,propertyEmbed,propertyOthers,references⟩
  · intro query above earlier outside away
    obtain ⟨middleOutside,middleWord⟩ := prefixFrame.words query above earlier outside
    obtain ⟨nextOutside,nextWord⟩ := frame query above (by omega) middleOutside away
    exact ⟨nextOutside,nextWord.trans middleWord⟩
  · intro reader
    obtain ⟨kind,floor,pointer⟩ := metadata reader
    exact ⟨kind.trans (prefixMetadata.kinds reader),floor.trans (prefixMetadata.floors reader),pointer.trans (prefixMetadata.pointers reader)⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.Result.prepend_mutation
