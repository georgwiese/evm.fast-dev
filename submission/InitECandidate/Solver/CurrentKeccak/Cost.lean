import InitECandidate.Solver.CurrentKeccak.PaddingCost
import InitECandidate.Solver.Input.ClockCostScopeLocals

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input Input.CounterFlow

set_option maxRecDepth 10000

def bodyPrice (length : Nat) := 44*(length/136)+689

theorem after_blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (word : BitVec 64)
    (small : length+136<2^64) (installed : OriginalCode.Installed source.code)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (bounded : word.toNat≤length) (short : length-word.toNat<136) :
    source.clock-(evaluateHOLFiniteState source afterBlocks).2.clock≤432 := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : BitVec.ofNat 64 length-word=BitVec.ofNat 64 (length-word.toNat):=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change word.toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact bounded),number,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have read : eval source remainder=some (.val (.word (BitVec.ofNat 64 (length-word.toNat)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,remainder,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [afterBlocks_shape]
  exact ClockCost.declared_current source "rem" remainder (BitVec.ofNat 64 (length-word.toNat)) paddingTail 432 read
    (padding_cost (WitnessRadix.QueryBranch.bind source "rem" (BitVec.ofNat 64 (length-word.toNat))) (length-word.toNat) short installed (bind_lookup_same _ _ _))

theorem loop_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+136<2^64) (installed : OriginalCode.Installed source.code) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.seq blocks afterBlocks)).2.clock≤44*(length/136)+432 := by
  apply ClockCost.sequence_reached_current source blocks afterBlocks (44*(length/136)) 432 (blocks_cost source length small installed valid)
  intro middle normal
  obtain ⟨word,counter,count,bounded,short⟩:=blocks_normal source middle length small valid normal
  have sameCode:=(evaluation_fields source middle blocks none normal).2.2.2
  exact after_blocks_cost middle length word small (by rw [sameCode]; exact installed) counter count bounded short

/-- Every outcome of actual Software keccak256 has a linear block allowance plus
fixed initialization/padding/output work. Pointer mapping and future successful buffer reads are not entry premises. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+136<2^64) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice length := by
  rw [body_shape]
  apply ClockCost.scalar_declaration_current source (ofString "stp") (.var .global (ofString "keccak_st")) _ (bodyPrice length)
  intro stp
  let declared:=WitnessRadix.QueryBranch.bind source "stp" stp
  have declaredCount : declared.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "stp" "n" stp (by decide)).trans count
  have zero:=BufferDynamicCost.zero_cost declared (localVar "stp") (.const 200#64) 200 installed (by decide) rfl
  have zeroPrice : declared.clock-(evaluateHOLFiniteState declared (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])).2.clock≤257:=zero
  have combined:=ClockCost.sequence_reached_current declared _ _ 257 (44*(length/136)+432) zeroPrice (by
    intro middle normal
    have nextCount : middle.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
      (CallNormal.ignored_lookup declared middle (ofString "n") (ofString "memzero") [localVar "stp",.const 200#64] normal).trans declaredCount
    have sameCode:=(evaluation_fields declared middle _ none normal).2.2.2
    have nextInstalled : OriginalCode.Installed middle.code:=by rw [sameCode]; exact installed
    apply ClockCost.declared_current middle "i" (.const 0#64) 0#64 (.seq blocks afterBlocks) (44*(length/136)+432) rfl
    exact loop_tail_cost (WitnessRadix.QueryBranch.bind middle "i" 0#64) length small nextInstalled
      ⟨0#64,bind_lookup_same _ _ _,(bind_lookup_other middle "i" "n" 0#64 (by decide)).trans nextCount,by simp⟩)
  have total : 257+(44*(length/136)+432)=bodyPrice length:=by unfold bodyPrice; omega
  rw [total] at combined
  exact combined

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat) (small : length+136<2^64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)).2.clock≤bodyPrice length+1 := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=environment source.code.lookup pointer out length (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "keccak256") arguments (values pointer out length) body callee .one (bodyPrice length)
    args called (body_cost (callEntryStateHOLFinite source callee) length small installed countCell)

/-- A fixed spatial allowance for every actual 64-bit requested count. -/
def domainBodyPrice : Nat := 44*domainBlockRank 0#64+689

theorem domainBodyPrice_value : domainBodyPrice=10937265093 := by decide

private theorem domain_loop_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp : BitVec 64) (installed : OriginalCode.Installed source.code)
    (ready : DomainBlockState pointer count stp source 0#64) :
    source.clock-(evaluateHOLFiniteState source (.seq blocks afterBlocks)).2.clock≤44*domainBlockRank 0#64+432 := by
  apply ClockCost.sequence_reached_current source blocks afterBlocks (44*domainBlockRank 0#64) 432
    (blocks_domain_cost source pointer count stp 0#64 installed ready)
  intro middle normal
  obtain ⟨word,valid,short,bounded⟩:=blocks_domain_normal source middle pointer count stp 0#64 installed ready normal
  have small : count.toNat+136<2^64 := by unfold CopyAny.ordinaryEnd at bounded; omega
  have sameCode:=(evaluation_fields source middle blocks none normal).2.2.2
  exact after_blocks_cost middle count.toNat word small (by rw [sameCode]; exact installed)
    valid.counter (by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using valid.countCell) valid.belowCount short

/-- The unchanged software hash has a uniform spatial allowance even for
arbitrarily large cached counts. Success of any later read is not assumed. -/
theorem body_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤domainBodyPrice := by
  rw [body_shape]
  apply ClockCost.scalar_declaration_current source (ofString "stp") (.var .global (ofString "keccak_st")) _ domainBodyPrice
  intro stp
  let declared:=WitnessRadix.QueryBranch.bind source "stp" stp
  have declaredPointer : declared.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other source "stp" "p" stp (by decide)).trans pointerCell
  have declaredCount : declared.locals.lookup (ofString "n")=some (.val (.word count)) :=
    (bind_lookup_other source "stp" "n" stp (by decide)).trans countCell
  have zeroPrice : declared.clock-(evaluateHOLFiniteState declared
      (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])).2.clock≤257 :=
    BufferDynamicCost.zero_cost declared (localVar "stp") (.const 200#64) 200 installed (by decide) rfl
  have combined:=ClockCost.sequence_reached_current declared _ _ 257 (44*domainBlockRank 0#64+432) zeroPrice (by
    intro middle normal
    have keep (key : MlS) : middle.locals.lookup key=declared.locals.lookup key :=
      CallNormal.ignored_lookup declared middle key (ofString "memzero") [localVar "stp",.const 200#64] normal
    have nextPointer:=(keep (ofString "p")).trans declaredPointer
    have nextCount:=(keep (ofString "n")).trans declaredCount
    have nextState:=(keep (ofString "stp")).trans (bind_lookup_same source "stp" stp)
    have fields:=evaluation_fields declared middle _ none normal
    have nextInstalled : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact installed
    have nextDomain : middle.memaddrs=InitE.ordinaryDomain := fields.1.trans domain
    apply ClockCost.declared_current middle "i" (.const 0#64) 0#64 (.seq blocks afterBlocks) (44*domainBlockRank 0#64+432) rfl
    let entry:=WitnessRadix.QueryBranch.bind middle "i" 0#64
    have ready : DomainBlockState pointer count stp entry 0#64 :=
      ⟨nextDomain,(bind_lookup_other middle "i" "p" 0#64 (by decide)).trans nextPointer,
        (bind_lookup_other middle "i" "n" 0#64 (by decide)).trans nextCount,
        (bind_lookup_other middle "i" "stp" 0#64 (by decide)).trans nextState,
        bind_lookup_same _ _ _,by simp,by simp,by intro impossible; exact (impossible rfl).elim⟩
    exact domain_loop_tail_cost entry pointer count stp nextInstalled ready)
  have total : 257+(44*domainBlockRank 0#64+432)=domainBodyPrice := by rfl
  rw [total] at combined
  exact combined

theorem call_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)).2.clock≤domainBodyPrice+1 := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=environment source.code.lookup pointer out length (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "keccak256") arguments (values pointer out length) body callee .one domainBodyPrice
    args called (body_domain_cost (callEntryStateHOLFinite source callee) pointer (BitVec.ofNat 64 length) installed domain pointerCell countCell)

/-- A real returning hash derives the small-count condition needed by the
existing padding and memory frames. This is an output fact, not an entry assumption. -/
theorem body_count_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp : BitVec 64) (installed : OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (stateGlobal : source.globals.lookup (ofString "keccak_st")=some (.val (.word stp)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    count.toNat<CopyAny.ordinaryEnd+272 := by
  rw [body_shape] at run
  have stateRead : eval source (.var .global (ofString "keccak_st"))=some (.val (.word stp)) := by
    simp [eval,evalHOLExact,toExact,stateGlobal]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source post "stp" _ stp _ value stateRead run
  let entry:=WitnessRadix.QueryBranch.bind source "stp" stp
  have entryPointer : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other source "stp" "p" stp (by decide)).trans pointerCell
  have entryCount : entry.locals.lookup (ofString "n")=some (.val (.word count)) :=
    (bind_lookup_other source "stp" "n" stp (by decide)).trans countCell
  obtain ⟨zeroed,zeroRun,afterZero⟩:=Input.sequence_returned entry inner _ _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by intro name impossible; cases impossible)).summary_full entry).2.1 continued
  have keep (key : MlS) : zeroed.locals.lookup key=entry.locals.lookup key :=
    CallNormal.ignored_lookup entry zeroed key (ofString "memzero") [localVar "stp",.const 200#64] zeroRun
  have nextPointer:=(keep (ofString "p")).trans entryPointer
  have nextCount:=(keep (ofString "n")).trans entryCount
  have nextState:=(keep (ofString "stp")).trans (bind_lookup_same source "stp" stp)
  have fields:=evaluation_fields entry zeroed _ none zeroRun
  have nextInstalled : OriginalCode.Installed zeroed.code := by rw [fields.2.2.2]; exact installed
  have nextDomain : zeroed.memaddrs=InitE.ordinaryDomain := fields.1.trans domain
  obtain ⟨loopPost,loopReturned,iRestored⟩:=Input.declaration_return_word zeroed inner "i" (.const 0#64) 0#64 _ value rfl afterZero
  let loopEntry:=WitnessRadix.QueryBranch.bind zeroed "i" 0#64
  have ready : DomainBlockState pointer count stp loopEntry 0#64 :=
    ⟨nextDomain,(bind_lookup_other zeroed "i" "p" 0#64 (by decide)).trans nextPointer,
      (bind_lookup_other zeroed "i" "n" 0#64 (by decide)).trans nextCount,
      (bind_lookup_other zeroed "i" "stp" 0#64 (by decide)).trans nextState,
      bind_lookup_same _ _ _,by simp,by simp,by intro impossible; exact (impossible rfl).elim⟩
  have safe : LocalPrefix (ofString "n") blocks := .loop condition block_safe
  obtain ⟨middle,blocksRun,afterRun⟩:=Input.sequence_returned loopEntry loopPost blocks afterBlocks value (safe.summary_full loopEntry).2.1 loopReturned
  exact (blocks_domain_normal loopEntry middle pointer count stp 0#64 nextInstalled ready blocksRun).choose_spec.2.2

/-- Preserve length-sensitive pricing for small inputs and cap it by the
uniform spatial allowance for large requested counts. -/
def boundedBodyPrice (length : Nat) : Nat := bodyPrice (min length (CopyAny.ordinaryEnd+272))

theorem boundedBodyPrice_mono (length limit : Nat) (bounded : length≤limit) :
    boundedBodyPrice length≤boundedBodyPrice limit := by
  have clipped : min length (CopyAny.ordinaryEnd+272)≤min limit (CopyAny.ordinaryEnd+272) := by omega
  have quotient:=Nat.div_le_div_right (c:=136) clipped
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 44 quotient) 689

theorem boundedBodyPrice_small (length : Nat) (bounded : length≤CopyAny.ordinaryEnd+272) :
    boundedBodyPrice length=bodyPrice length := by
  rw [boundedBodyPrice,Nat.min_eq_left bounded]

theorem body_bounded_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤boundedBodyPrice length := by
  by_cases small : length≤CopyAny.ordinaryEnd+272
  · rw [boundedBodyPrice_small length small]
    have fits : length+136<2^64 := by unfold CopyAny.ordinaryEnd at small; omega
    exact body_cost source length fits installed countCell
  · have price : boundedBodyPrice length=domainBodyPrice := by
      rw [boundedBodyPrice,Nat.min_eq_right (by omega)]
      rfl
    rw [price]
    exact body_domain_cost source pointer (BitVec.ofNat 64 length) installed domain pointerCell countCell

theorem call_bounded_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)).2.clock≤boundedBodyPrice length+1 := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=environment source.code.lookup pointer out length (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "keccak256") arguments (values pointer out length) body callee .one (boundedBodyPrice length)
    args called (body_bounded_cost (callEntryStateHOLFinite source callee) pointer length installed domain pointerCell countCell)

theorem boundedBodyPrice_le (length : Nat) : boundedBodyPrice length≤bodyPrice length := by
  have clipped : min length (CopyAny.ordinaryEnd+272)≤length := Nat.min_le_left _ _
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 44 (Nat.div_le_div_right clipped)) 689

/-- Compatibility with the original linear allowance, now for every actual
count. Large counts are covered by the sharper spatial ceiling above. -/
theorem call_any_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)).2.clock≤bodyPrice length+1 :=
  (call_bounded_cost source arguments pointer out length installed domain args).trans
    (Nat.add_le_add_right (boundedBodyPrice_le length) 1)

theorem boundedBodyPrice_le_domain (length : Nat) : boundedBodyPrice length≤domainBodyPrice := by
  have clipped : min length (CopyAny.ordinaryEnd+272)≤CopyAny.ordinaryEnd+272 := Nat.min_le_right _ _
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 44 (Nat.div_le_div_right clipped)) 689

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.after_blocks_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.loop_tail_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_domain_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_domain_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_count_bound

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.domainBodyPrice_value

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.boundedBodyPrice_mono
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.boundedBodyPrice_small
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_bounded_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_bounded_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.boundedBodyPrice_le
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_any_length_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.boundedBodyPrice_le_domain
