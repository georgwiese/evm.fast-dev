import InitECandidate.Solver.Mpt.AccountBalanceSetResult

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

variable {ι : Type} [Fintype ι]
variable {source ready post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {cursor readyCursor cutoff population base cap count : Nat} {objects middle : ι → TableFamily.Object} {accountWriter : ι}
variable {accounts middleAccounts : List (BitVec 64)} {property : ι → BitVec 64 → Prop} {budget : Bool → Bool → Nat → Nat}

theorem Result.locals (result : Result source post cursor cutoff population objects accountWriter base cap count accounts property budget)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    Result source {post with locals := locals} cursor cutoff population objects accountWriter base cap count accounts property budget := by
  obtain ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,price,codes,
    environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩ := result
  let finish := {post with locals := locals}
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have finalRegistry := registry.framed post finish cutoff nextCursor nextCursor next next nextAccounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next post finish rfl) (Nat.le_refl _) rfl
  exact ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,finalFamily,finalImage,zone,price,codes,
    environment.of_fields rfl rfl rfl,globals,values,saved,finalRegistry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩

theorem Result.prepend_mutation (result : Result ready post readyCursor cutoff population middle accountWriter base cap count middleAccounts property budget)
    (prefixPaid prefixPrice : Nat) (fundedPrefix : prefixPaid ≤ source.clock)
    (prefixBound : prefixPaid + TableFamily.potential objects ≤ prefixPrice + TableFamily.potential middle)
    (readyClock : ready.clock = source.clock - prefixPaid) (forwardPrefix : cursor ≤ readyCursor)
    (prefixExtension : AccountDecode.Registry.Extension accounts middleAccounts cursor)
    (prefixFrame : TableFamily.PersistentFrame cutoff cursor objects middle source ready)
    (prefixMetadata : TableFamily.Metadata objects middle) (prefixGlobals : HeapGlobals source ready) (readyCode : ready.code = source.code) :
    Result source post cursor cutoff population objects accountWriter base cap count accounts property (fun destroyed found iterations => prefixPrice + budget destroyed found iterations) := by
  obtain ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,price,codes,
    environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩ := result
  rw [readyClock] at funded clock
  have totalFunded : prefixPaid + paid ≤ source.clock := by
    calc
      _ ≤ prefixPaid + (source.clock - prefixPaid) := Nat.add_le_add_left funded _
      _ = source.clock := Nat.add_sub_of_le fundedPrefix
  have totalClock : post.clock = source.clock - (prefixPaid + paid) := by rw [clock,Nat.sub_sub]
  have totalGlobals : Journal.OtherGlobals source post := by
    intro name notHeap notCounter
    exact (globals name notHeap notCounter).trans (prefixGlobals name notHeap)
  have prefixEffect := Journal.CounterEffect.unchanged source ready (prefixGlobals (ofString "journal_n") (by decide))
  have totalEffect : Journal.CounterEffect source post added 0 0 := by
    simpa only [Nat.zero_add,Nat.add_zero] using prefixEffect.trans effect
  refine ⟨freshCursor,prefixPaid + paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,by omega,prefixExtension.trans extension forwardPrefix,
    totalFunded,totalClock,by omega,addedPositive,addedBound,capacityBound,models,image,zone,by dsimp only; omega,codes.trans readyCode,
    environment,totalGlobals,values,saved,registry,totalEffect,prefixMetadata.trans metadata,?_,counter,appends,visits,freshMember,populations⟩
  intro query above earlier outside away
  obtain ⟨middleOutside,middleWord⟩ := prefixFrame.words query above earlier outside
  obtain ⟨nextOutside,nextWord⟩ := frame query above (by omega) middleOutside away
  exact ⟨nextOutside,nextWord.trans middleWord⟩

theorem Result.mono (result : Result source post cursor cutoff population objects accountWriter base cap count accounts property budget)
    (other : Bool → Bool → Nat → Nat) (larger : ∀ destroyed found iterations,budget destroyed found iterations ≤ other destroyed found iterations) :
    Result source post cursor cutoff population objects accountWriter base cap count accounts property other := by
  obtain ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,price,codes,
    environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩ := result
  exact ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,
    Nat.le_trans price (Nat.add_le_add_right (larger destroyed found iterations) _),codes,environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.Result.locals
#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.Result.prepend_mutation
#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.Result.mono
