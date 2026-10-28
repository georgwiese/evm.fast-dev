import InitECandidate.Solver.CurrentKeccak.PaddingCost
import InitECandidate.Solver.Input.ClockCostScopeLocals

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input Input.CounterFlow

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

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.after_blocks_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.loop_tail_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_cost
