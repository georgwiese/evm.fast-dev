import InitECandidate.Solver.Mpt.StorageSetResult

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

variable {ι : Type} [Fintype ι]
variable {source ready post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {cursor cutoff population base cap count : Nat} {objects : ι → TableFamily.Object} {outer : ι}
variable {accounts : List (BitVec 64)} {property : ι → BitVec 64 → Prop} {budget : Bool → Nat}

theorem Result.locals (result : Result source post cursor cutoff population objects outer base cap count accounts property budget)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    Result source {post with locals := locals} cursor cutoff population objects outer base cap count accounts property budget := by
  obtain ⟨κ,finite,embed,next,nextProperty,paid,nextCursor,added,created,nextEntries,injective,card,funded,clock,forward,appends,room,models,image,zone,price,populations,codes,
    environment,globals,values,saved,registry,effect,frame,metadata,counter,propertyEmbed,propertyOthers,references⟩ := result
  let finish := {post with locals := locals}
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have finalRegistry := registry.framed post finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next post finish rfl) (Nat.le_refl _) rfl
  exact ⟨κ,finite,embed,next,nextProperty,paid,nextCursor,added,created,nextEntries,injective,card,funded,clock,forward,appends,room,finalFamily,finalImage,zone,price,populations,codes,
    environment.of_fields rfl rfl rfl,globals,values,saved,finalRegistry,effect,frame,metadata,counter,propertyEmbed,propertyOthers,references⟩

theorem Result.prepend_readonly (result : Result ready post cursor cutoff population objects outer base cap count accounts property budget)
    (prefixPaid prefixPrice : Nat) (fundedPrefix : prefixPaid ≤ source.clock) (prefixBound : prefixPaid ≤ prefixPrice)
    (readyClock : ready.clock = source.clock - prefixPaid) (readyGlobals : ready.globals = source.globals)
    (readyMemory : ready.memory = source.memory) (readyCode : ready.code = source.code) :
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
    exact (globals name notHeap notCounter).trans (congrArg (fun map => map.lookup name) readyGlobals)
  have totalEffect : Journal.CounterEffect source post added 0 0 := by
    simpa only [Journal.CounterEffect,Journal.currentCount,readyGlobals] using effect
  refine ⟨κ,finite,embed,next,nextProperty,prefixPaid + paid,nextCursor,added,created,nextEntries,injective,card,totalFunded,totalClock,forward,appends,room,models,image,zone,
    by dsimp only; omega,populations,codes.trans readyCode,environment,totalGlobals,values,saved,registry,totalEffect,?_,metadata,counter,propertyEmbed,propertyOthers,references⟩
  intro query earlier outside away
  obtain ⟨nextOutside,equal⟩ := frame query earlier outside away
  exact ⟨nextOutside,equal.trans (congrFun readyMemory query)⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.Result.locals
#print axioms InitECandidate.Solver.Mpt.StorageSet.Result.prepend_readonly
