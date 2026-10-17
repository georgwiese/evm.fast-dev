import InitECandidate.Solver.MutableTable.WitnessBuildRecordStep
import InitECandidate.Solver.MutableTable.WitnessBuildSetFfi

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Compose a supplied actual hash call with the complete original map
update and increment, retaining its concrete digest, FFI and public frame. -/
theorem record_step_with_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (scratch : BitVec 64) (count index : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Layout32.Built bits source plan scratch count input logical) (processed : input.length=index) (inside : index<plan.count)
    (locals : Locals source plan index) (slices : Nat→Graph.Slice) (records : Records source plan slices)
    (stp pad : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch)))
    (buffers : Keccak256.Buffers stp (slices index).1 pad scratch (slices index).2.toNat)
    (before : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ scratch.toNat+32≤plan.records)
    (aligned : scratch.toNat%8=0) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one))
    (hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hashRun : evaluateHOLFiniteState source
      (.call (some (none,none)) (ofString "keccak256") Constructor.hashArguments)=(none,hashed))
    (hashLocals : hashed.locals=source.locals) (hashUpper : hashed.clock≤source.clock)
    (hashLower : source.clock-(Keccak256.price (slices index).2.toNat+1)≤hashed.clock)
    (hashControl : KeccakAbsorb.hashControl hashed=KeccakAbsorb.hashControl source)
    (hashMemory : ∀ query,Keccak256.Protected stp pad scratch query→hashed.memory query=source.memory query)
    (enough : recordPrice (slices index).2.toNat index≤source.clock) :
    ∃ key slot nextCount target,slot<plan.capacity ∧ count≤nextCount ∧ nextCount≤count+1 ∧
      evaluateHOLFiniteState source recordBody=(none,target) ∧
      Layout32.Built bits target plan scratch nextCount (input++[(key,recordAddress plan index)]) (Placement.put logical slot key (recordAddress plan index)) ∧
      Locals target plan (index+1) ∧ Records target plan slices ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧ target.clock≤source.clock ∧
      source.clock-recordPrice (slices index).2.toNat index≤target.clock ∧
      (∀ name : MlS,ofString "i"≠name→target.locals.lookup name=source.locals.lookup name) ∧
      key=WordKeys.key (MemoryBytes.wordsOf hashed scratch) ∧ target.ffi=hashed.ffi ∧
      (∀ query,query.toNat<plan.table→target.memory query=hashed.memory query) := by
  have tableBefore : stp.toNat+200≤plan.table ∧ pad.toNat+136≤plan.table ∧ scratch.toNat+32≤plan.table := by
    have:=ready.recordsBefore
    omega
  have hashBuilt:=Layout32.built_after_hash source hashed plan ready bits scratch count input logical stp (slices index).1 pad scratch
    (slices index).2.toNat buffers tableBefore hashControl hashMemory built
  have hashRecords:=Records.after_hash source hashed plan ready slices stp (slices index).1 pad scratch (slices index).2.toNat buffers before hashMemory records
  have hashDomain : hashed.memaddrs=source.memaddrs:=congrArg (fun s=>s.memaddrs) hashControl
  have hashEndian : hashed.be=source.be:=congrArg (fun s=>s.be) hashControl
  have codes : hashed.code=source.code:=congrArg (fun s=>s.code) hashControl
  have globals : hashed.globals=source.globals:=congrArg (fun s=>s.globals) hashControl
  have hashLocalFacts : Locals hashed plan index := by
    rcases locals with ⟨a,b,c,d⟩
    constructor <;> rw [hashLocals] <;> assumption
  let words:=MemoryBytes.wordsOf hashed scratch
  let key:=WordKeys.key words
  have wordView : MemoryBytes.WordView hashed scratch words := by
    constructor
    · intro limb
      exact AllocatedBytes.word_mapped hashed scratch 32 (8*limb.val) (hashDomain.trans domain) buffers.outputArena
        (by have:=limb.isLt;omega) aligned (by omega)
    · intro limb
      unfold words MemoryBytes.wordsOf
      cases hashed.memory (scratch+BitVec.ofNat 64 (8*limb.val))
      rfl
  have scratchFits : scratch.toNat+32<2^64:=by have:=buffers.outputArena.upper;omega
  have digest : MemoryBytes.ByteView hashed scratch key:=MemoryBytes.wordView_bytes hashed scratch words aligned scratchFits (hashEndian.trans little) wordView
  obtain ⟨slot,nextCount,paid,target,slotInside,countLower,countUpper,bound,suffixRun,next,finalLocals,control,clock,earlier,others,suffixFfi⟩:=
    after_hash_step_with_ffi hashed plan ready (hashDomain.trans domain) scratch count index input logical bits small power hashBuilt processed inside hashLocalFacts key words
      (by rw [globals];exact global) aligned tableBefore.2.2 (hashEndian.trans little) wordView digest
      (by rw [codes];exact hashCode) (by rw [codes];exact copyCode) (by rw [codes];exact insertCode)
      (by rw [codes];exact memeqCode) (by rw [codes];exact findCode) (by rw [codes];exact setCode)
      (by unfold recordPrice at enough;omega)
  refine ⟨key,slot,nextCount,target,slotInside,countLower,countUpper,?_,next,finalLocals,
    Records.of_earlier hashed target plan ready slices earlier hashRecords,control.trans hashControl,?_,?_,?_,rfl,suffixFfi,earlier⟩
  · rw [recordBody,StateSteps.next_sequence source hashed _ _ hashRun hashUpper]
    exact suffixRun
  · rw [clock];omega
  · rw [clock]
    unfold recordPrice at enough ⊢
    omega
  · intro name different
    rw [others name different,hashLocals]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.record_step_with_hash
