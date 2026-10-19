import InitECandidate.Solver.Mpt.StorageSetNewPrefix
import InitECandidate.Solver.Mpt.StorageSetValue

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem new_branch_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address query : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (outerKind : (objects outer).kind = .account) (addressArena : AllocatedBytes.Arena address 20) (queryArena : AllocatedBytes.Arena query 32)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (innerLocal : source.locals.lookup (ofString "inner") = some (.val (.word 0#64)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source newBranch = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ count + 2 ≤ cap ∧ ∃ (paid nextCursor : Nat) (next : Option ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry (Option ι)),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + 2) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity + GrowRuntime.growthPotential .word 8 ≤
        TableRuntime.price 8 + Journal.Append.setPrice (objects outer).kind (objects outer).slots.length + Journal.Append.setPrice .word 0 + 4 +
          GrowRuntime.growthPotential (objects outer).kind (next (some outer)).plan.capacity + GrowRuntime.growthPotential .word (next none).plan.capacity ∧
      (next (some outer)).slots.length ≤ (objects outer).slots.length + 1 ∧ (next none).slots.length ≤ 1 ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      TableFamily.ValuesHave post next (newProperty property outer cursor) ∧ Journal.EntryValues nextEntries (count + 2) (newProperty property outer cursor) ∧
      AccountDecode.Registry post cutoff nextCursor next accounts ∧ Journal.CounterEffect source post 2 0 0 ∧
      (∀ query : BitVec 64,query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query → TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      TableFamily.Metadata (TableFamily.extend objects (Journal.newObject .word cursor 8)) next ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 2)))) ∧
      (∀ reader,reader ≠ outer → next (some reader) = objects reader) := by
  obtain ⟨firstRoom,prefixPaid,readyCursor,published,firstFlag,firstValue,ready,prefixFunded,prefixClock,prefixForward,readyFamily,readyImage,readyZone,prefixPrice,publishedCount,
    readyCode,readyEnvironment,readyGlobals,readyValues,readySaved,readyRegistry,prefixEffect,prefixFrame,prefixMetadata,readyCounter,readyLocals,tailRun⟩ :=
    new_prefix_normal source post address cursor cutoff objects outer base cap count entries family image zone countBound environment installed accounts registry accountApart property values savedValues outerKind addressArena
      addressLocal outerLocal innerLocal journal capacity counter returned normal
  let extended := TableFamily.extend objects (Journal.newObject .word cursor 8)
  let readyObjects := Function.update extended (some outer) published
  let readyEntries := Function.update (fun index => (entries index).lift) count ⟨some outer,BitVec.ofNat 64 (freshEnd .word cursor 8),firstFlag,firstValue⟩
  have freshSame : readyObjects none = Journal.newObject .word cursor 8 := by simp [readyObjects,extended,TableFamily.extend]
  have freshPointer : (readyObjects none).pointer = BitVec.ofNat 64 cursor := by rw [freshSame]; rfl
  have freshKind : (readyObjects none).kind = .word := by rw [freshSame]; rfl
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "inner" ≠ ofString "key" by decide] using queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "inner" ≠ ofString "value" by decide] using valueLocal
  have readyInner : ready.locals.lookup (ofString "inner") = some (.val (.word (readyObjects none).pointer)) := by
    rw [readyLocals,freshPointer]
    simp [HolFiniteMapExact.update,FUPDATE]
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [readyCode]; exact installed
  obtain ⟨secondRoom,answerEq,valuePaid,nextCursor,inner,secondFlag,secondValue,valueFunded,valueClock,valueForward,models,nextImage,nextZone,valuePrice,innerCount,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,valueEffect,valueFrame,valueMetadata,nextCounter⟩ := allocate_tail_normal ready post query words readyCursor cutoff readyObjects none base cap (count + 1) readyEntries
      readyFamily readyImage readyZone (by omega) readyEnvironment readyInstalled accounts readyRegistry accountApart (newProperty property outer cursor) readyValues readySaved
      (fun pointer arena aligned => Or.inl ⟨arena,aligned⟩) freshKind queryArena readyQuery readyValue readyInner
      ((readyGlobals (ofString "journal") (by decide) (by decide)).trans journal) ((readyGlobals (ofString "journal_cap") (by decide) (by decide)).trans capacity) readyCounter returned tailRun
  let next := Function.update readyObjects none inner
  let nextEntries := Function.update readyEntries (count + 1) ⟨none,BitVec.ofNat 64 (readyCursor + 32),secondFlag,secondValue⟩
  have outerSame : next (some outer) = published := by simp [next,readyObjects]
  have innerSame : next none = inner := by simp [next]
  have freshSlots : (readyObjects none).slots = [] := by rw [freshSame]; rfl
  have freshCapacity : (readyObjects none).plan.capacity = 8 := by rw [freshSame]; rfl
  rw [freshKind,freshSlots,freshCapacity] at valuePrice
  rw [freshSlots] at innerCount
  change valuePaid + GrowRuntime.growthPotential .word 8 ≤ Journal.Append.setPrice .word 0 + 2 + GrowRuntime.growthPotential .word inner.plan.capacity at valuePrice
  have funded : prefixPaid + valuePaid ≤ source.clock := by
    rw [prefixClock] at valueFunded
    calc
      _ ≤ prefixPaid + (source.clock - prefixPaid) := Nat.add_le_add_left valueFunded _
      _ = source.clock := Nat.add_sub_of_le prefixFunded
  have clock : post.clock = source.clock - (prefixPaid + valuePaid) := by rw [valueClock,prefixClock,Nat.sub_sub]
  have totalGlobals := readyGlobals.trans globals
  have totalEffect : Journal.CounterEffect source post 2 0 0 := by
    simpa only [Nat.add_zero] using prefixEffect.trans valueEffect
  have totalMetadata := prefixMetadata.trans valueMetadata
  have totalPrice : prefixPaid + valuePaid + GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity + GrowRuntime.growthPotential .word 8 ≤
      TableRuntime.price 8 + Journal.Append.setPrice (objects outer).kind (objects outer).slots.length + Journal.Append.setPrice .word 0 + 4 +
        GrowRuntime.growthPotential (objects outer).kind (next (some outer)).plan.capacity + GrowRuntime.growthPotential .word (next none).plan.capacity := by
    rw [outerSame,innerSame]
    omega
  refine ⟨answerEq,by omega,prefixPaid + valuePaid,nextCursor,next,nextEntries,funded,clock,by dsimp only [freshEnd] at prefixForward; omega,models,?_,nextZone,totalPrice,by rw [outerSame]; exact publishedCount,
    by rw [innerSame]; simpa using innerCount,codes.trans readyCode,nextEnvironment,totalGlobals,nextValues,?_,nextRegistry,totalEffect,?_,totalMetadata,?_,?_⟩
  · simpa only [Nat.add_assoc] using nextImage
  · simpa only [Nat.add_assoc] using nextSaved
  · intro query earlier outside away
    obtain ⟨readyOutside,readyWord⟩ := prefixFrame query earlier outside away
    have readyEarlier : query.toNat < readyCursor := by dsimp only [freshEnd] at prefixForward; omega
    obtain ⟨nextOutside,nextWord⟩ := valueFrame.words query readyEarlier readyOutside away
    exact ⟨nextOutside,nextWord.trans readyWord⟩
  · simpa only [Nat.add_assoc] using nextCounter
  · intro reader other
    simp [next,readyObjects,extended,TableFamily.extend,other]

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.new_branch_normal
