import InitECandidate.Solver.Input.Copy32SpanWrites
import InitECandidate.Solver.WitnessRadix.CopyFreshFrame
import InitECandidate.Solver.Input.LocalSummaryConditional
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.ConditionalNone
import InitECandidate.Solver.Input.CopyAnyFlow
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.LoadOneWord

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

def price (length : Nat) : Nat:=length/32+length/8+length/8+length

theorem Loop.uniform_cost (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤length/loop.stride:=
  loop.cost length small source valid

private theorem conditional_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (yes no : ProgHOL 64) (length : Nat)
    (left : evaluateHOLFiniteState source yes=(none,post)→StrideInvariant length post)
    (right : evaluateHOLFiniteState source no=(none,post)→StrideInvariant length post)
    (normal : evaluateHOLFiniteState source (.ite test yes no)=(none,post)) : StrideInvariant length post:=by
  exact (Input.conditional_none source post test yes no normal).elim left right

theorem aligned_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.seq Copy32.loop32 Copy32.loopWord)).2.clock≤length/32+length/8:=by
  exact ClockCost.sequence_reached_current source Copy32.loop32 Copy32.loopWord (length/32) (length/8)
    (Loop.block32.uniform_cost length small source valid) (fun middle normal=>Loop.word.uniform_cost length small middle (Loop.block32.normal length small source middle valid normal))

theorem aligned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source (.seq Copy32.loop32 Copy32.loopWord)=(none,post)) : StrideInvariant length post:=by
  obtain ⟨middle,front,back⟩:=sequence_none source post _ _ normal
  exact Loop.word.normal length small middle post (Loop.block32.normal length small source middle valid front) back

theorem after_alignment_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64))))).2.clock≤length/8+length:=by
  apply ClockCost.sequence_reached_current source Copy32.loopBytes _ (length/8) length
    (Loop.bytes.uniform_cost length small source valid)
  intro middle normal
  have next:=Loop.bytes.normal length small source middle valid normal
  have tail:=Loop.tail.uniform_cost length small middle next
  have result:=ClockCost.sequence_current middle Copy32.loopTail (.return (.const 0#64)) length 0 (by simpa only [Loop.program,Loop.stride,Loop.zeroLoop,ZeroAny.Loop.stride,Nat.div_one] using tail)
    (ClockCost.returned middle.code _)
  simpa only [Nat.add_zero] using result

/-- All original memcpy outcomes, with no pointer, alignment, mapping,
successful store, allocator-room or future-execution premise. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source Copy32.body).2.clock≤price length:=by
  rw [Copy32.body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ (price length) rfl
  let entry:=bind source "i" 0#64
  have initial : StrideInvariant length entry:=⟨0#64,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by simp⟩
  have front:=ClockCost.conditional_current entry Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip (length/32+length/8) 0
    (aligned_cost entry length small initial) (ClockCost.skip entry.code entry rfl)
  simp only [Nat.max_zero] at front
  have combined:=ClockCost.sequence_reached_current entry (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)
    (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64)))) (length/32+length/8) (length/8+length) front (by
      intro middle normal
      have valid : StrideInvariant length middle:=conditional_normal entry middle _ _ _ length
        (aligned_normal entry middle length small initial) (by intro skipped; rw [evaluateHOLFiniteState_skip] at skipped; have same:entry=middle:=congrArg Prod.snd skipped; rewrite [←same]; exact initial) normal
      exact after_alignment_cost middle length small valid)
  simpa only [price,Nat.add_assoc] using combined

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst src : BitVec 64) (length : Nat) (small : length+32<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (CopyGeneral.values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock≤price length+1:=by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩:=CopyGeneral.environment source.code.lookup dst src length code
  exact ClockCost.call_current source (some none) (ofString "memcpy") arguments (CopyGeneral.values dst src length) Copy32.body callee .one (price length)
    args called (body_cost (callEntryStateHOLFinite source callee) length small lengthCell)

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.uniform_cost
#print axioms InitECandidate.Solver.Input.CopyAny.aligned_cost
#print axioms InitECandidate.Solver.Input.CopyAny.aligned_normal
#print axioms InitECandidate.Solver.Input.CopyAny.after_alignment_cost
#print axioms InitECandidate.Solver.Input.CopyAny.body_cost
#print axioms InitECandidate.Solver.Input.CopyAny.call_cost

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

/-- The exact exclusive upper end of the fixed ordinary word domain. -/
def ordinaryEnd : Nat:=33806089704

theorem ordinary_bounds (pointer : BitVec 64) (mapped : InitE.ordinaryDomain pointer) :
    2701131776≤pointer.toNat ∧ pointer.toNat<ordinaryEnd ∧ pointer.toNat%8=0 := by
  change Flapjack.Compiler.Backend.StackRemove.addresses 2701131776#64 3888119741 pointer at mapped
  obtain ⟨index,inside,equal⟩:=(Flapjack.Compiler.Backend.StackRemove.mem_addresses _ _ _).mp mapped
  have product : (BitVec.ofNat 64 index*8#64).toNat=index*8:=by
    rw [←BitVec.ofNat_mul,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have number : pointer.toNat=2701131776+index*8:=by
    rw [equal]
    change (2701131776#64+BitVec.ofNat 64 index*8#64).toNat=_
    rw [BitVec.toNat_add_of_lt (by rw [product]; change 2701131776+index*8<2^64; omega),product]
    rfl
  rw [number]
  unfold ordinaryEnd
  omega

theorem ordinary_byte_upper (pointer : BitVec 64)
    (mapped : InitE.ordinaryDomain (panByteAlignHOL (width:=64) pointer)) : pointer.toNat<ordinaryEnd := by
  have upper:=(ordinary_bounds _ mapped).2.1
  rw [AllocatedBytes.aligned_number] at upper
  unfold ordinaryEnd at upper ⊢
  omega

/-- Successful ordinary byte stores derive their real backing-word mapping. -/
theorem byte_store_mapped (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination expression : ExpHOL 64) (address : BitVec 64)
    (readAddress : eval source destination=some (.val (.word address)))
    (normal : evaluateHOLFiniteState source (.storeByte destination expression)=(none,target)) :
    source.memaddrs (panByteAlignHOL (width:=64) address) := by
  classical
  by_contra absent
  simp only [eval] at readAddress
  rw [evaluateHOLFiniteState_storeByte,readAddress] at normal
  generalize readValue : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun query=>Classical.propDecidable (source.memaddrs query)) expression=value at normal
  cases value with
  | none=>cases normal
  | some value=>
    cases value with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word value=>
        cases cell : source.memory (panByteAlignHOL (width:=64) address) with
        | word old=>simp only [panMemStoreByteWord8HOL,cell,if_neg absent] at normal; cases normal

private theorem word_first_upper (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64)
    (tail : ProgHOL 64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (destination : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (normal : evaluateHOLFiniteState source (.seq (Copy32.wordStore 0) tail)=(none,target)) :
    (dst+index).toNat<ordinaryEnd := by
  obtain ⟨middle,stored,remaining⟩:=sequence_none source target _ _ normal
  have read : eval source (Copy32.address "dst" 0)=some (.val (.word (dst+index))):=by
    simpa only [BitVec.add_zero] using CopyBytes.address_read source "dst" dst index 0 destination counter
  obtain ⟨value,memory,valueRead,stores,changed⟩:=store_at_normal source middle (Copy32.address "dst" 0) (.load .one (Copy32.address "src" 0)) _ read stored
  obtain ⟨word,rfl⟩:=load_one_word source (Copy32.address "src" 0) value valueRead
  have mapped:=(word_store_normal source middle _ _ _ word read valueRead stored).1
  rw [domain] at mapped
  exact (ordinary_bounds _ mapped).2.1

private theorem byte_first_upper (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64)
    (tail : ProgHOL 64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (destination : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (normal : evaluateHOLFiniteState source (.seq (CopyBytes.store 0) tail)=(none,target)) :
    (dst+index).toNat<ordinaryEnd := by
  obtain ⟨middle,stored,remaining⟩:=sequence_none source target _ _ normal
  have read : eval source (Copy32.address "dst" 0)=some (.val (.word (dst+index))):=by
    simpa only [BitVec.add_zero] using CopyBytes.address_read source "dst" dst index 0 destination counter
  have mapped:=byte_store_mapped source middle _ _ _ read stored
  rw [domain] at mapped
  exact ordinary_byte_upper _ mapped

/-- Every genuine normal copy block must write its first destination cell.
This caps spatial progress even when the requested length is near 2^64. -/
theorem Loop.first_upper (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (destination : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (normal : evaluateHOLFiniteState source loop.block=(none,target)) : (dst+index).toNat<ordinaryEnd := by
  cases loop with
  | block32=>exact word_first_upper source target dst index _ domain destination counter normal
  | word=>exact word_first_upper source target dst index _ domain destination counter normal
  | bytes=>exact byte_first_upper source target dst index _ domain destination counter normal
  | tail=>exact byte_first_upper source target dst index _ domain destination counter normal

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.ordinary_bounds
#print axioms InitECandidate.Solver.Input.CopyAny.ordinary_byte_upper
#print axioms InitECandidate.Solver.Input.CopyAny.byte_store_mapped
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.first_upper

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

private theorem word_destination_summary (offsets : List Nat) (tail : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "dst") tail source) :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "dst") (CopyWords.stores offsets tail) source := by
  induction offsets with
  | nil=>exact safe
  | cons offset rest ih=>exact local_summary_sequence _ _ _ (LocalPrefix.store _ _).summary_full ih

private theorem byte_destination_summary (offsets : List Nat) (tail : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "dst") tail source) :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "dst") (CopyBytes.stores offsets tail) source := by
  induction offsets with
  | nil=>exact safe
  | cons offset rest ih=>exact local_summary_sequence _ _ _ (byte_store_local _ _ _) ih

theorem Loop.destination_summary (loop : Loop) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    LocalSummary (ofString "dst") loop.block source := by
  have increment (stride : Nat) : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      LocalSummary (ofString "dst") (CopyBytes.increment (BitVec.ofNat 64 stride)) source:=
    (LocalPrefix.assign (key:=ofString "dst") (ofString "i") _ (by decide)).summary_full
  cases loop with
  | block32=>exact word_destination_summary [0,8,16,24] _ (increment 32) source
  | word=>exact word_destination_summary [0] _ (increment 8) source
  | bytes=>exact byte_destination_summary [0,1,2,3,4,5,6,7] _ (increment 8) source
  | tail=>exact byte_destination_summary [0] _ (increment 1) source

def room (dst : BitVec 64) : Nat:=ordinaryEnd-dst.toNat

def Spatial (dst : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∃ index : BitVec 64,source.memaddrs=InitE.ordinaryDomain ∧
    source.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧
    source.locals.lookup (ofString "i")=some (.val (.word index)) ∧
    index.toNat≤room dst+31 ∧ (index=0#64 ∨ dst.toNat<ordinaryEnd)

def spatialRank (dst : BitVec 64) (stride : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  (room dst+31-(counterWord source (ofString "i")).toNat)/stride+1

theorem spatial_number (dst index : BitVec 64) (bounded : index.toNat≤room dst+31)
    (feasible : index=0#64 ∨ dst.toNat<ordinaryEnd) : (dst+index).toNat=dst.toNat+index.toNat := by
  rcases feasible with rfl|inside
  · simp
  · exact BitVec.toNat_add_of_lt (by unfold room at bounded; unfold ordinaryEnd at bounded inside; omega)

/-- A genuine continuing copy block cannot wrap its counter: its first
successful physical write already puts it below the ordinary-memory end. -/
theorem Loop.spatial_step (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (valid : Spatial dst source) (normal : evaluateHOLFiniteState source loop.block=(none,target)) :
    Spatial dst target ∧ spatialRank dst loop.stride target<spatialRank dst loop.stride source := by
  obtain ⟨index,domain,destination,counter,bounded,feasible⟩:=valid
  have positive : 0<loop.stride:=by cases loop <;> decide
  have strideBound : loop.stride≤32:=by cases loop <;> decide
  have upper:=loop.first_upper source target dst index domain destination counter normal
  rw [spatial_number dst index bounded feasible] at upper
  have below : index.toNat<room dst:=by unfold room; omega
  have dstBound : dst.toNat<ordinaryEnd:=by omega
  have roomBound : room dst≤ordinaryEnd:=Nat.sub_le _ _
  have strideSmall : (BitVec.ofNat 64 loop.stride).toNat=loop.stride:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nextNumber : (index+BitVec.ofNat 64 loop.stride).toNat=index.toNat+loop.stride:=by
    rw [BitVec.toNat_add_of_lt (by rw [strideSmall]; unfold ordinaryEnd at roomBound; omega),strideSmall]
  have nextCounter:=(loop.block_model source.code).advance source target index counter normal
  have safe:=loop.destination_summary source
  unfold LocalSummary at safe
  rw [normal] at safe
  have nextDst:=(safe.1 rfl).trans destination
  have nextDomain:=(evaluation_fields source target loop.block none normal).1.trans domain
  have before : spatialRank dst loop.stride source=(room dst+31-index.toNat)/loop.stride+1:=by
    simp [spatialRank,counterWord,counter,valueWord]
  have after : spatialRank dst loop.stride target=(room dst+31-(index.toNat+loop.stride))/loop.stride+1:=by
    simp [spatialRank,counterWord,nextCounter,valueWord,nextNumber]
  refine ⟨⟨index+BitVec.ofNat 64 loop.stride,nextDomain,nextDst,nextCounter,?_,Or.inr dstBound⟩,?_⟩
  · rw [nextNumber]
    omega
  · have difference : room dst+31-index.toNat=(room dst+31-(index.toNat+loop.stride))+loop.stride:=by omega
    rw [after,before,difference,Nat.add_div_right _ positive]
    omega

/-- Spatial ranking includes the last failing iteration. It therefore
covers every requested length, including values whose loop guards wrap. -/
theorem Loop.spatial_cost (loop : Loop) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (valid : Spatial dst source) : source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤spatialRank dst loop.stride source := by
  have model:=loop.block_model source.code
  have bounded:=ClockCost.ranked_loop_current source.code loop.zeroLoop.test loop.block 0 (Spatial dst) (spatialRank dst loop.stride) (by
    intro state codeEq ready word observed nonzero funded
    exact (ClockCost.of_quiet source.code _ model.quiet) (decClockHOLFinite state) codeEq) (by
    intro state codeEq ready word observed nonzero
    refine ⟨by exact Nat.zero_lt_succ _,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite state) loop.block
    have safe:=loop.destination_summary (decClockHOLFinite state)
    unfold LocalSummary at safe
    have normal : output.1=none:=continuing.resolve_right safe.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) loop.block=(none,output.2):=Prod.ext normal rfl
    exact loop.spatial_step (decClockHOLFinite state) output.2 dst ready run) source rfl valid
  rw [Loop.shape]
  simpa only [Nat.zero_add,Nat.one_mul] using bounded

theorem Loop.spatial_normal (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (valid : Spatial dst source) (normal : evaluateHOLFiniteState source loop.program=(none,target)) : Spatial dst target := by
  rw [Loop.shape] at normal
  apply loop_invariant_no_control source.code loop.zeroLoop.test loop.block
    (fun state=>⟨(loop.destination_summary state).2.2.1,(loop.destination_summary state).2.2.2⟩) (Spatial dst) ?_ source target rfl valid normal
  intro state codeEq ready word observed nonzero funded post run
  exact (loop.spatial_step (decClockHOLFinite state) post dst ready run).1

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.destination_summary
#print axioms InitECandidate.Solver.Input.CopyAny.spatial_number
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.spatial_step
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.spatial_cost
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.spatial_normal

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

def domainLoopPrice (dst : BitVec 64) (stride : Nat) : Nat:=(room dst+31)/stride+1
def domainPrice (dst : BitVec 64) : Nat:=domainLoopPrice dst 32+domainLoopPrice dst 8+domainLoopPrice dst 8+domainLoopPrice dst 1

theorem Loop.domain_cost (loop : Loop) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (valid : Spatial dst source) : source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤domainLoopPrice dst loop.stride := by
  have ranked:=loop.spatial_cost source dst valid
  have bounded : spatialRank dst loop.stride source≤domainLoopPrice dst loop.stride:=
    Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) 1
  exact Nat.le_trans ranked bounded

theorem aligned_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (valid : Spatial dst source) :
    source.clock-(evaluateHOLFiniteState source (.seq Copy32.loop32 Copy32.loopWord)).2.clock≤domainLoopPrice dst 32+domainLoopPrice dst 8 := by
  exact ClockCost.sequence_reached_current source Copy32.loop32 Copy32.loopWord _ _
    (Loop.block32.domain_cost source dst valid) (fun middle normal=>Loop.word.domain_cost middle dst (Loop.block32.spatial_normal source middle dst valid normal))

theorem aligned_domain_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (valid : Spatial dst source) (normal : evaluateHOLFiniteState source (.seq Copy32.loop32 Copy32.loopWord)=(none,target)) : Spatial dst target := by
  obtain ⟨middle,first,second⟩:=sequence_none source target _ _ normal
  exact Loop.word.spatial_normal middle target dst (Loop.block32.spatial_normal source middle dst valid first) second

theorem after_alignment_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (valid : Spatial dst source) :
    source.clock-(evaluateHOLFiniteState source (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64))))).2.clock≤domainLoopPrice dst 8+domainLoopPrice dst 1 := by
  apply ClockCost.sequence_reached_current source Copy32.loopBytes _ _ _ (Loop.bytes.domain_cost source dst valid)
  intro middle normal
  have reached:=Loop.bytes.spatial_normal source middle dst valid normal
  have result:=ClockCost.sequence_current middle Copy32.loopTail (.return (.const 0#64)) (domainLoopPrice dst 1) 0
    (Loop.tail.domain_cost middle dst reached) (ClockCost.returned middle.code _)
  simpa only [Nat.add_zero] using result

/-- Every outcome of unchanged memcpy is bounded in the actual ordinary
memory domain, for arbitrary requested lengths and source-pointer contents. -/
theorem body_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (destination : source.locals.lookup (ofString "dst")=some (.val (.word dst))) :
    source.clock-(evaluateHOLFiniteState source Copy32.body).2.clock≤domainPrice dst := by
  rw [Copy32.body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ _ rfl
  let entry:=bind source "i" 0#64
  have initial : Spatial dst entry:=⟨0#64,domain,(bind_lookup_other source "i" "dst" 0#64 (by decide)).trans destination,
    bind_lookup_same _ _ _,by simp,Or.inl rfl⟩
  have front:=ClockCost.conditional_current entry Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip
    (domainLoopPrice dst 32+domainLoopPrice dst 8) 0 (aligned_domain_cost entry dst initial) (ClockCost.skip entry.code entry rfl)
  simp only [Nat.max_zero] at front
  have combined:=ClockCost.sequence_reached_current entry (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)
    (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64)))) _ _ front (by
      intro middle normal
      have reached : Spatial dst middle:=by
        rcases conditional_none entry middle Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip normal with aligned|skipped
        · exact aligned_domain_normal entry middle dst initial aligned
        · have same : entry=middle:=by simpa only [evaluateHOLFiniteState_skip] using congrArg Prod.snd skipped
          rw [←same]
          exact initial
      exact after_alignment_domain_cost middle dst reached)
  simpa only [domainPrice,Nat.add_assoc] using combined

/-- The genuine three-word original ABI supplies the destination binding;
no bound or nonwrapping hypothesis on its requested length is required. -/
theorem call_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst src : BitVec 64) (length : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (CopyGeneral.values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock≤domainPrice dst+1 := by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩:=CopyGeneral.environment source.code.lookup dst src length code
  exact ClockCost.call_current source (some none) (ofString "memcpy") arguments (CopyGeneral.values dst src length) Copy32.body callee .one
    (domainPrice dst) args called (body_domain_cost (callEntryStateHOLFinite source callee) dst domain dstCell)

theorem domain_price_uniform (dst : BitVec 64) : domainPrice dst≤43314052475 := by
  have bounded : room dst≤ordinaryEnd:=Nat.sub_le _ _
  unfold domainPrice domainLoopPrice
  unfold ordinaryEnd at bounded
  omega

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.domain_cost
#print axioms InitECandidate.Solver.Input.CopyAny.aligned_domain_cost
#print axioms InitECandidate.Solver.Input.CopyAny.aligned_domain_normal
#print axioms InitECandidate.Solver.Input.CopyAny.after_alignment_domain_cost
#print axioms InitECandidate.Solver.Input.CopyAny.body_domain_cost
#print axioms InitECandidate.Solver.Input.CopyAny.call_domain_cost
#print axioms InitECandidate.Solver.Input.CopyAny.domain_price_uniform

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

theorem Loop.writes (loop : Loop) : Copy32Span.Writes loop.stride loop.block := by
  cases loop with
  | block32=>exact Copy32Span.Writes.words (size:=32) [0,8,16,24] (by simp) 32
  | word=>exact Copy32Span.Writes.words (size:=8) [0] (by simp) 8
  | bytes=>exact Copy32Span.Writes.bytes (size:=8) [0,1,2,3,4,5,6,7] (by simp) 8
  | tail=>exact Copy32Span.Writes.bytes (size:=1) [0] (by simp) 1

/-- Actual normal blocks retain runtime metadata and all words below an
older aligned frontier. Spatial progress rules out wrapping store addresses. -/
theorem Loop.spatial_frame (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst query : BitVec 64) (floor : Nat) (valid : Spatial dst source)
    (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (normal : evaluateHOLFiniteState source loop.block=(none,target)) :
    Spatial dst target ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.memory query=source.memory query := by
  have entered:=valid
  obtain ⟨index,domain,destination,counter,bounded,feasible⟩:=valid
  have strideBound : loop.stride≤32:=by cases loop <;> decide
  have upper:=loop.first_upper source target dst index domain destination counter normal
  rw [spatial_number dst index bounded feasible] at upper
  have dstSmall : dst.toNat<ordinaryEnd:=by omega
  obtain ⟨frame,nextDst⟩:=loop.writes.normal source target dst index (room dst+64) (by omega) destination counter normal
  refine ⟨(loop.spatial_step source target dst entered normal).1,frame.fields,?_⟩
  apply frame.memory
  exact CopyGeneral.Away.after_floor dst query (room dst+64) floor aligned afterFloor
    (by unfold room; unfold ordinaryEnd at dstSmall ⊢; omega) beforeFloor

theorem Loop.spatial_loop_frame (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst query : BitVec 64) (floor : Nat) (valid : Spatial dst source)
    (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (normal : evaluateHOLFiniteState source loop.program=(none,target)) :
    Spatial dst target ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Spatial dst current ∧
    MemoryMetadata.erase current=MemoryMetadata.erase source ∧ current.memory query=source.memory query
  rw [Loop.shape] at normal
  apply loop_invariant_no_control source.code loop.zeroLoop.test loop.block
    (fun current=>(loop.destination_summary current).2.2) invariant ?_ source target rfl ⟨valid,rfl,rfl⟩ normal
  intro current installed reached word observed nonzero funded post run
  obtain ⟨ready,metadata,memory⟩:=reached
  obtain ⟨next,fields,written⟩:=loop.spatial_frame (decClockHOLFinite current) post dst query floor ready aligned afterFloor beforeFloor run
  exact ⟨next,fields.trans metadata,written.trans memory⟩

private theorem alignment_domain_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst query : BitVec 64) (floor : Nat) (valid : Spatial dst source)
    (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (normal : evaluateHOLFiniteState source (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)=(none,target)) :
    Spatial dst target ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.memory query=source.memory query := by
  rcases conditional_none source target Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip normal with copied|skipped
  · obtain ⟨middle,first,second⟩:=sequence_none source target _ _ copied
    obtain ⟨middleValid,firstFields,firstWord⟩:=Loop.block32.spatial_loop_frame source middle dst query floor valid aligned afterFloor beforeFloor first
    obtain ⟨lastValid,lastFields,lastWord⟩:=Loop.word.spatial_loop_frame middle target dst query floor middleValid aligned afterFloor beforeFloor second
    exact ⟨lastValid,lastFields.trans firstFields,lastWord.trans firstWord⟩
  · have same : target=source:=by simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm
    rw [same]
    exact ⟨valid,rfl,rfl⟩

/-- Every real returning copy preserves its earlier-memory frame, without
an entry limit on its requested length or any source/destination mapping oracle. -/
theorem body_domain_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query count : BitVec 64) (floor : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (destination : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Copy32.body=(some (.returned value),target)) :
    count.toNat≤room dst+31 ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.memory query=source.memory query := by
  have loopSummary (loop : Loop) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : LocalSummary (ofString "dst") loop.program current:=by
    rw [Loop.shape]
    exact while_local_summary _ _ _ loop.destination_summary current
  have alignmentSummary : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      LocalSummary (ofString "dst") (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip) current:=
    local_summary_conditional _ _ _ _ (local_summary_sequence _ _ _ (loopSummary .block32) (loopSummary .word)) LocalPrefix.skip.summary_full
  have countSummary (loop : Loop) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : LocalSummary (ofString "n") loop.program current:=by
    rw [Loop.shape]
    exact while_local_summary _ _ _ (loop.block_model source.code).summary current
  have countAlignment : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      LocalSummary (ofString "n") (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip) current:=
    local_summary_conditional _ _ _ _ (local_summary_sequence _ _ _ (countSummary .block32) (countSummary .word)) LocalPrefix.skip.summary_full
  have keepCount (first last : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
      (safe : LocalSummary (ofString "n") program first)
      (cell : first.locals.lookup (ofString "n")=some (.val (.word count)))
      (actual : evaluateHOLFiniteState first program=(none,last)) : last.locals.lookup (ofString "n")=some (.val (.word count)):=by
    unfold LocalSummary at safe
    rw [actual] at safe
    exact (safe.1 rfl).trans cell
  rw [Copy32.body_shape] at normal
  obtain ⟨inner,run,endpoint⟩:=ScalarScope.declare_trace source target "i" (.const 0#64) 0#64 _ (some (.returned value)) rfl normal
  let entry:=bind source "i" 0#64
  have initial : Spatial dst entry:=⟨0#64,domain,(bind_lookup_other source "i" "dst" 0#64 (by decide)).trans destination,
    bind_lookup_same _ _ _,by simp,Or.inl rfl⟩
  obtain ⟨afterAlignment,alignedRun,remaining⟩:=sequence_returned entry inner _ _ value (alignmentSummary entry).2.1 run
  obtain ⟨alignmentValid,alignmentFields,alignmentWord⟩:=alignment_domain_frame entry afterAlignment dst query floor initial aligned afterFloor beforeFloor alignedRun
  obtain ⟨afterBytes,byteRun,remaining⟩:=sequence_returned afterAlignment inner _ _ value (loopSummary .bytes afterAlignment).2.1 remaining
  obtain ⟨bytesValid,bytesFields,bytesWord⟩:=Loop.bytes.spatial_loop_frame afterAlignment afterBytes dst query floor alignmentValid aligned afterFloor beforeFloor byteRun
  obtain ⟨afterTail,tailRun,returned⟩:=sequence_returned afterBytes inner _ _ value (loopSummary .tail afterBytes).2.1 remaining
  obtain ⟨tailValid,tailFields,tailWord⟩:=Loop.tail.spatial_loop_frame afterBytes afterTail dst query floor bytesValid aligned afterFloor beforeFloor tailRun
  have entryCount : entry.locals.lookup (ofString "n")=some (.val (.word count)):=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans countCell
  have alignmentCount:=keepCount entry afterAlignment _ (countAlignment entry) entryCount alignedRun
  have bytesCount:=keepCount afterAlignment afterBytes _ (countSummary .bytes afterAlignment) alignmentCount byteRun
  have tailCount:=keepCount afterBytes afterTail _ (countSummary .tail afterBytes) bytesCount tailRun
  have actualTail:=tailRun
  rw [Loop.shape] at actualTail
  have exited:=loop_normal_exit (.cmp .lower (localVar "i") (localVar "n")) CopyBytes.tailBody
    (fun current=>((Loop.tail.block_model source.code).summary current).2.2.1) afterBytes afterTail actualTail
  obtain ⟨lastIndex,lastDomain,lastDst,lastCounter,lastBound,lastFeasible⟩:=tailValid
  have countBound : count.toNat≤room dst+31:=by
    have expected : evalHOLFinite afterTail (h:=fun address=>Classical.propDecidable (afterTail.memaddrs address))
        (.cmp .lower (localVar "i") (localVar "n"))=
        some (.val (.word (if lastIndex.toNat<count.toNat then 1#64 else 0#64))):=by
      simp [evalHOLFinite,evalHOLExact,toExact,localVar,lastCounter,tailCount,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
    by_cases active : lastIndex.toNat<count.toNat
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact ((by decide : (0#64 : BitVec 64)≠1#64) impossible).elim
    · omega
  have returnFrame:=LocalEffects.returned afterTail.code (.const 0#64) afterTail rfl
  rw [returned] at returnFrame
  change LocalEffects.erase inner=LocalEffects.erase afterTail at returnFrame
  rw [endpoint]
  exact ⟨countBound,(MemoryMetadata.of_frame returnFrame).trans (tailFields.trans (bytesFields.trans alignmentFields)),
    (congrFun (LocalEffects.memory_of_erase afterTail inner returnFrame) query).trans (tailWord.trans (bytesWord.trans alignmentWord))⟩

/-- The same frame holds at a genuine ordinary caller, using its actual
child return and restored caller locals. -/
theorem call_domain_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst src query : BitVec 64) (length floor : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun current=>Classical.propDecidable (source.memaddrs current)) arguments=some (CopyGeneral.values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one))
    (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,target)) :
    (BitVec.ofNat 64 length).toNat≤room dst+31 ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.memory query=source.memory query := by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩:=CopyGeneral.environment source.code.lookup dst src length code
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,child,returned,actualArgs,actualCalled,run,checked,endpoint,fields⟩:=
    CallNormal.ignored_data source target (ofString "memcpy") arguments normal
  have sameValues : actualValues=CopyGeneral.values dst src length:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have same : (actualBody,actualCallee,actualShape)=(Copy32.body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  have frame:=body_domain_normal (callEntryStateHOLFinite source callee) child dst query (BitVec.ofNat 64 length) floor domain dstCell lengthCell aligned afterFloor beforeFloor returned run
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.writes
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.spatial_frame
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.spatial_loop_frame
#print axioms InitECandidate.Solver.Input.CopyAny.body_domain_normal
#print axioms InitECandidate.Solver.Input.CopyAny.call_domain_normal

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

/-- A real known-length copy loop writes only its actual destination span.
Successful source reads and destination stores are derived from this run. -/
theorem Loop.span_frame (loop : Loop) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst : BitVec 64) (length : Nat) (small : length+32<2^64)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source loop.program=(none,target)) :
    Copy32Span.Frame source target dst length ∧ target.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant length target := by
  have block:=loop.block_model source.code
  let invariant:=fun current=>Copy32Span.Frame source current dst length ∧
    current.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant length current
  rw [Loop.shape] at normal
  apply loop_invariant_no_control source.code loop.zeroLoop.test loop.block (fun current=>(block.summary current).2.2)
    invariant ?_ source target rfl ⟨Copy32Span.Frame.refl source dst length,dstCell,valid⟩ normal
  intro current installed reached observed actual nonzero funded post bodyRun
  obtain ⟨earlier,currentDst,currentCounter⟩:=reached
  have saved:=currentCounter
  obtain ⟨index,iCell,nCell,bounded⟩:=saved
  have reads : StrideReads loop.zeroLoop.test loop.stride length:=loop.zeroLoop.reads length small
  have expected:=reads current index iCell nCell bounded
  have active : index.toNat+loop.stride≤length:=by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
    exact nonzero zero
  obtain ⟨written,nextDst⟩:=loop.writes.normal (decClockHOLFinite current) post dst index length active currentDst iCell bodyRun
  have kept : Copy32Span.Frame current post dst length:=⟨written.fields,written.memory⟩
  have transition:=(stride_transition loop.zeroLoop.test loop.block loop.stride length (by cases loop <;> decide) (by omega)
    block.advance block.summary reads current currentCounter observed actual nonzero).2 funded
  rw [bodyRun] at transition
  exact ⟨earlier.trans source current post dst length kept,nextDst,(transition (Or.inl rfl)).1⟩

private theorem alignment_span_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst : BitVec 64) (length : Nat) (small : length+32<2^64)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)=(none,target)) :
    Copy32Span.Frame source target dst length ∧ target.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant length target := by
  rcases conditional_none source target Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip normal with copied|skipped
  · obtain ⟨middle,front,back⟩:=sequence_none source target _ _ copied
    obtain ⟨first,middleDst,middleValid⟩:=Loop.block32.span_frame source middle dst length small dstCell valid front
    obtain ⟨second,lastDst,lastValid⟩:=Loop.word.span_frame middle target dst length small middleDst middleValid back
    exact ⟨first.trans source middle target dst length second,lastDst,lastValid⟩
  · have same : target=source:=by simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm
    rw [same]
    exact ⟨Copy32Span.Frame.refl source dst length,dstCell,valid⟩

private theorem Loop.span_summary (loop : Loop) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    LocalSummary (ofString "dst") loop.program source := by
  rw [Loop.shape]
  exact while_local_summary (ofString "dst") loop.zeroLoop.test loop.block loop.destination_summary source

/-- Complete real normal memcpy at any known nonwrapping count. Neither
input/output ownership nor mapping is a premise of its exact write frame. -/
theorem body_span_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat)
    (small : length+32<2^64)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Copy32.body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ Copy32Span.Frame source post dst length := by
  rw [Copy32.body_shape] at normal
  obtain ⟨inner,remaining,endpoint⟩:=declaration_return_word source post "i" (.const 0#64) 0#64 _ value rfl normal
  let entry:=bind source "i" 0#64
  have entryDst : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans dstCell
  have initial : StrideInvariant length entry:=⟨0#64,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by simp⟩
  have alignedSummary:=local_summary_sequence (ofString "dst") Copy32.loop32 Copy32.loopWord
    Loop.block32.span_summary Loop.word.span_summary
  have choiceSummary:=local_summary_conditional (ofString "dst") Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip
    alignedSummary LocalPrefix.skip.summary_full
  obtain ⟨middle,choiceRun,byteTail⟩:=sequence_returned entry inner _ _ value (choiceSummary entry).2.1 remaining
  obtain ⟨front,middleDst,middleValid⟩:=alignment_span_frame entry middle dst length small entryDst initial choiceRun
  obtain ⟨last,byteRun,tailReturn⟩:=sequence_returned middle inner _ _ value (Loop.bytes.span_summary middle).2.1 byteTail
  obtain ⟨bytesFrame,lastDst,lastValid⟩:=Loop.bytes.span_frame middle last dst length small middleDst middleValid byteRun
  obtain ⟨finish,tailRun,returned⟩:=sequence_returned last inner _ _ value (Loop.tail.span_summary last).2.1 tailReturn
  obtain ⟨tailFrame,finishDst,finishValid⟩:=Loop.tail.span_frame last finish dst length small lastDst lastValid tailRun
  obtain ⟨read,innerEq⟩:=return_normal finish inner (.const 0#64) value returned
  have valueEq : value=.val (.word 0#64):=Option.some.inj read.symm
  have full:=(front.trans entry middle last dst length bytesFrame).trans entry last finish dst length tailFrame
  refine ⟨valueEq,?_,?_⟩
  · rw [endpoint,innerEq]
    exact full.fields
  · intro query away
    rw [endpoint,innerEq]
    exact full.memory query away

/-- Actual ignored caller, with exact span frame and restored caller locals,
without source/destination mapping or allocation assumptions. -/
theorem call_span_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat)
    (small : length+32<2^64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (CopyGeneral.values dst src length))
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) :
    Copy32Span.Frame source post dst length ∧ post.locals=source.locals := by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩:=CopyGeneral.environment source.code.lookup dst src length (CopyGeneral.original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "memcpy") arguments normal
  have sameValues : values=CopyGeneral.values dst src length:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have same : (actual,actualCallee,shape)=(Copy32.body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  obtain ⟨valueEq,frame⟩:=body_span_normal (callEntryStateHOLFinite source callee) target dst length small dstCell lengthCell value bodyRun
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [endpoint]
    exact frame.fields
  · intro query away
    rw [endpoint]
    exact frame.memory query away
  · rw [endpoint]

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.span_frame
#print axioms InitECandidate.Solver.Input.CopyAny.body_span_normal
#print axioms InitECandidate.Solver.Input.CopyAny.call_span_normal
