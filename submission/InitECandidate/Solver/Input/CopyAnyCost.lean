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
