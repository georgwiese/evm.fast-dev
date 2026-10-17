import InitECandidate.Solver.WitnessRadix.ConstructorRecordStep
import InitECandidate.Solver.WitnessRadix.ConstructorStepExact

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString

/-- One entire actual constructor record iteration: real record loads,
complete fixed hash call, digest copy, record/ordinal stores and increment.
The newly observed concrete digest extends the initialized prefix. -/
theorem record_step_with_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (valid : Valid layout)
    (mapped : Mapped source layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (index : Nat) (inside : index<layout.count)
    (locals : Locals source layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index))
    (prefixData : Prefix source layout keyFor index) (fixedData : FixedData source layout sliceFor)
    (stp padScratch hashScratch : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)))
    (environment : Keccak256.Environment source stp padScratch)
    (buffers : Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (before : ∀ pool,stp.toNat+200≤(base layout pool).toNat ∧ padScratch.toNat+136≤(base layout pool).toNat ∧ hashScratch.toNat+32≤(base layout pool).toNat)
    (scratchAligned : hashScratch.toNat%8=0) (little : source.be=false)
    (hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hashRun : evaluateHOLFiniteState source
      (.call (some (none,none)) (ofString "keccak256") hashArguments)=(none,hashed))
    (hashLocals : hashed.locals=source.locals) (hashUpper : hashed.clock≤source.clock)
    (hashLower : source.clock-(Keccak256.price (sliceFor (BitVec.ofNat 64 index)).2.toNat+1)≤hashed.clock)
    (hashControl : KeccakAbsorb.hashControl hashed=KeccakAbsorb.hashControl source)
    (hashMemory : ∀ query,Keccak256.Protected stp padScratch hashScratch query→hashed.memory query=source.memory query)
    (enough : recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat≤source.clock) :
    ∃ key : ByteKeys.Key,∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source recordBody=(none,target) ∧
      Prefix target layout (setKey keyFor index key) (index+1) ∧ FixedData target layout sliceFor ∧ Mapped target layout ∧
      Locals target layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 (index+1)) ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧ target.clock≤source.clock ∧
      source.clock-recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat≤target.clock ∧
      (∀ name : MlS,ofString "i"≠name → target.locals.lookup name=source.locals.lookup name) ∧
      key=WordKeys.key (MemoryBytes.wordsOf hashed hashScratch) ∧
      target=suffixState hashed layout index (MemoryBytes.wordsOf hashed hashScratch) ∧ target.ffi=hashed.ffi := by
  classical
  have frame := PoolFrame.of_hash source hashed layout valid stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch
    (sliceFor (BitVec.ofNat 64 index)).2.toNat buffers hashControl hashMemory before
  have hashMapped := PoolFrame.mapped source hashed layout frame mapped
  have hashFixed := PoolFrame.fixed_data source hashed layout frame sliceFor fixedData
  have hashPrefix := PoolFrame.prefix source hashed layout valid frame keyFor index (Nat.le_of_lt inside) prefixData
  have hashLocalFacts : Locals hashed layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index) := by
    rcases locals with ⟨a,b,c,d,e⟩
    constructor <;> rw [hashLocals] <;> assumption
  have hashDomain : hashed.memaddrs=InitE.ordinaryDomain := frame.domain.trans environment.domain
  have scratchFits : hashScratch.toNat+32<2^64 := by have := buffers.outputArena.upper; omega
  let words := MemoryBytes.wordsOf hashed hashScratch
  let key := WordKeys.key words
  have wordView : MemoryBytes.WordView hashed hashScratch words := by
    constructor
    · intro limb
      exact AllocatedBytes.word_mapped hashed hashScratch 32 (8*limb.val) hashDomain buffers.outputArena
        (by have := limb.isLt; omega) scratchAligned (by omega)
    · intro limb
      unfold words MemoryBytes.wordsOf
      cases hashed.memory (hashScratch+BitVec.ofNat 64 (8*limb.val))
      rfl
  have hashLittle : hashed.be=false := frame.endian.trans little
  have digest : MemoryBytes.ByteView hashed hashScratch key := MemoryBytes.wordView_bytes hashed hashScratch words scratchAligned scratchFits hashLittle wordView
  have rekeyed := Prefix.rekey_current hashed layout valid keyFor index key inside hashPrefix
  have digestFor : MemoryBytes.ByteView hashed hashScratch (setKey keyFor index key (BitVec.ofNat 64 index)) := by
    rw [setKey_current]
    exact digest
  have hashGlobal : hashed.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)) := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup (ofString "mpt_hash_scratch")) hashControl
    exact h.trans global
  have hashCopyCode : hashed.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one) := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code.lookup (ofString "memcpy")) hashControl
    exact h.trans environment.copyCode
  obtain ⟨finished,suffixRun,suffixPrefix,suffixFixed,suffixMapped,suffixLocals,suffixControl,suffixClock,suffixOther,suffixEq⟩ :=
    after_hash_step_exact hashed layout valid hashMapped (setKey keyFor index key) sliceFor index inside hashLocalFacts rekeyed hashFixed hashScratch
      hashGlobal hashCopyCode scratchAligned scratchFits (before .keys).2.2 digestFor hashLittle
      (by unfold recordPrice at enough; omega)
  have suffixHashControl := KeccakAbsorb.hashControl_of_control hashed finished suffixControl
  refine ⟨key,finished,?_,suffixPrefix,suffixFixed,suffixMapped,suffixLocals,suffixHashControl.trans hashControl,?_,?_,?_,rfl,suffixEq,?ffi⟩
  case ffi => exact congrArg (fun state => state.ffi) suffixControl
  · rw [recordBody,StateSteps.next_sequence source hashed _ _ hashRun hashUpper]
    exact suffixRun
  · rw [suffixClock]
    omega
  · rw [suffixClock]
    unfold recordPrice at enough ⊢
    omega
  · intro name different
    rw [suffixOther name different,hashLocals]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.record_step_with_hash
