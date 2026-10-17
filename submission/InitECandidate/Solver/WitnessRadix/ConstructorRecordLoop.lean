import InitECandidate.Solver.WitnessRadix.ConstructorHashContext

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString

/-- The complete actual constructor record loop initializes all hash,
record-pointer and ordinal arrays. Digests are the observed actual hash-call
outputs; no cryptographic or per-iteration execution oracle is assumed. -/
theorem record_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64) (maximum index remaining : Nat)
    (keyFor : BitVec 64 → ByteKeys.Key) (sizeEq : index+remaining=layout.count)
    (mapped : Mapped source layout)
    (locals : Locals source layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 layout.count))))
    (prefixData : Prefix source layout keyFor index) (fixedData : FixedData source layout sliceFor)
    (context : HashContext source layout sliceFor stp padScratch hashScratch maximum)
    (enough : (recordPrice maximum+1)*remaining≤source.clock) :
    ∃ finalKeys : BitVec 64 → ByteKeys.Key,∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source recordLoop=(none,output) ∧
      Prefix output layout finalKeys layout.count ∧ FixedData output layout sliceFor ∧ Mapped output layout ∧
      Locals output layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 layout.count) ∧
      KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧ output.clock≤source.clock ∧
      source.clock-(recordPrice maximum+1)*remaining≤output.clock ∧
      (∀ name : MlS,ofString "i"≠name → output.locals.lookup name=source.locals.lookup name) ∧
      (∀ old<index,finalKeys (BitVec.ofNat 64 old)=keyFor (BitVec.ofNat 64 old)) := by
  classical
  have countSmall : layout.count<2^64 := by have := count_small layout valid; omega
  induction remaining generalizing source index keyFor with
  | zero =>
    have same : index=layout.count := by omega
    have testRun := Zero.tail_condition source index layout.count countSmall (by omega) locals.indexLocal countLocal
    change @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition=
      some (.val (.word (if index<layout.count then 1#64 else 0#64))) at testRun
    have inactive : ¬index<layout.count := by omega
    simp only [if_neg inactive] at testRun
    refine ⟨keyFor,source,?_,?_,fixedData,mapped,?_,rfl,Nat.le_refl _,by simp,?_,?_⟩
    · rw [loop_shape,evaluateHOLFiniteState_while_total,testRun]; simp
    · simpa only [same] using prefixData
    · simpa only [same] using locals
    · intro name different; rfl
    · intro old earlier; rfl
  | succ remaining ih =>
    simp only [Nat.mul_succ] at enough
    have inside : index<layout.count := by omega
    have positive : source.clock≠0 := by omega
    let entry := decClockHOLFinite source
    have entryFrame : PoolFrame source entry layout := ⟨rfl,rfl,by intro pool offset bound; rfl⟩
    have entryMapped := PoolFrame.mapped source entry layout entryFrame mapped
    have entryPrefix := PoolFrame.prefix source entry layout valid entryFrame keyFor index (by omega) prefixData
    have entryFixed := PoolFrame.fixed_data source entry layout entryFrame sliceFor fixedData
    have entryContext := HashContext.of_control source entry layout sliceFor stp padScratch hashScratch maximum rfl context
    have entryLocals : Locals entry layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index) :=
      ⟨locals.keysLocal,locals.valsLocal,locals.orderLocal,locals.recordsLocal,locals.indexLocal⟩
    have currentBound := recordPrice_mono (sliceFor (BitVec.ofNat 64 index)).2.toNat maximum (context.lengthBound index inside)
    obtain ⟨key,next,bodyRun,bodyPrefix,bodyFixed,bodyMapped,bodyLocals,bodyControl,bodyUpper,bodyLower,bodyOther⟩ :=
      record_step entry layout valid entryMapped keyFor sliceFor index inside entryLocals entryPrefix entryFixed stp padScratch hashScratch
        entryContext.scratchGlobal entryContext.code entryContext.environment (context.buffers index inside) context.before context.scratchAligned context.little
        (by change recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat≤source.clock-1; omega)
    have nextContext := HashContext.of_control entry next layout sliceFor stp padScratch hashScratch maximum bodyControl entryContext
    have nextCount : next.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 layout.count))) :=
      (bodyOther (ofString "n") (by decide)).trans countLocal
    have bodyBudget : source.clock-1-recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat≤next.clock := bodyLower
    obtain ⟨finalKeys,output,tailRun,tailPrefix,tailFixed,tailMapped,tailLocals,tailControl,tailUpper,tailLower,tailOther,tailKeys⟩ :=
      ih next (index+1) (setKey keyFor index key) (by omega) bodyMapped bodyLocals nextCount bodyPrefix bodyFixed nextContext (by omega)
    refine ⟨finalKeys,output,?_,tailPrefix,tailFixed,tailMapped,tailLocals,tailControl.trans bodyControl,?_,?_,?_,?_⟩
    · have testRun := Zero.tail_condition source index layout.count countSmall (by omega) locals.indexLocal countLocal
      change @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition=
        some (.val (.word (if index<layout.count then 1#64 else 0#64))) at testRun
      simp only [if_pos inside] at testRun
      rw [loop_shape,evaluateHOLFiniteState_while_total,testRun]
      simp only [show (1#64 : BitVec 64)≠(0 : BitVec 64) from by decide,↓reduceIte,if_neg positive]
      rw [bodyRun,StateSteps.fixed_clock entry next none bodyUpper]
      split
      · change evaluateHOLFiniteState next (.while condition recordBody)=(none,output)
        rw [←loop_shape]
        exact tailRun
      · rename_i impossible
        exact (impossible (by decide)).elim
    · change next.clock≤source.clock-1 at bodyUpper
      omega
    · change next.clock-(recordPrice maximum+1)*remaining≤output.clock at tailLower
      simp only [Nat.mul_succ]
      omega
    · intro name different
      exact (tailOther name different).trans (bodyOther name different)
    · intro old earlier
      exact (tailKeys old (by omega)).trans (setKey_earlier layout valid keyFor index key inside old earlier)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.record_loop
