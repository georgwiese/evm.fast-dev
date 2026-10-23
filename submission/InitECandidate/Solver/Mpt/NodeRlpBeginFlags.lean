import InitECandidate.Solver.Mpt.NodeRlpBeginCompactNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def leafFlag : ProgHOL 64:=.ite (.cmp .equal (localVar "k") (.const 1#64)) (.assign .local (ofString "isl") (.const 1#64)) .skip

def CompactData.bind_leaf (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property) (leaf : BitVec 64) :
    CompactData (bind source "isl" leaf) node tag buffer pathLength limit property :={
  pointer:=data.pointer
  leaf:=leaf
  nodeCell:=(bind_lookup_other source "isl" "node" leaf (by decide)).trans data.nodeCell
  tagCell:=(bind_lookup_other source "isl" "k" leaf (by decide)).trans data.tagCell
  bufferCell:=(bind_lookup_other source "isl" "cbuf" leaf (by decide)).trans data.bufferCell
  pathCell:=(bind_lookup_other source "isl" "nlen" leaf (by decide)).trans data.pathCell
  leafCell:=bind_lookup_same _ _ _
  pointerMapped:=data.pointerMapped
  pointerStored:=data.pointerStored
  bufferMapped:=data.bufferMapped
  value:=data.value
  valueAway:=data.valueAway }

theorem leaf_flag_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (normal : evaluateHOLFiniteState source leafFlag=(none,target)) :
    target=if tag=1#64 then bind source "isl" 1#64 else source := by
  have selected : evaluateHOLFiniteState source leafFlag=
      if tag=1#64 then evaluateHOLFiniteState source (.assign .local (ofString "isl") (.const 1#64)) else (none,source):=by
    rw [leafFlag,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  by_cases leaf : tag=1#64
  · rw [if_pos leaf] at selected ⊢
    exact Input.assign_none source target "isl" (.const 1#64) 1#64 rfl (selected.symm.trans normal)
  · rw [if_neg leaf] at selected ⊢
    exact congrArg Prod.snd (normal.symm.trans selected)

theorem after_flag (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property)
    (normal : evaluateHOLFiniteState source leafFlag=(none,target)) :
    Nonempty (CompactData target node tag buffer pathLength limit property) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have same:=leaf_flag_normal source target tag data.tagCell normal
  by_cases leaf : tag=1#64
  · rw [if_pos leaf] at same
    rw [same]
    exact ⟨⟨data.bind_leaf source node tag buffer pathLength limit property 1#64⟩,rfl⟩
  · rw [if_neg leaf] at same
    rw [same]
    exact ⟨⟨data⟩,rfl⟩

theorem after_leaf_flag_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterLeafFlag).2.clock≤pathLength.toNat/2+24 := by
  rw [path_shapes.2.2.2.1]
  have price : Input.ClockCost.Bound source.code leafFlag 0:=Input.ClockCost.conditional source.code _ _ _ 0 0
    (Input.ClockCost.assign source.code _ _) (Input.ClockCost.skip source.code)
  have cost:=Input.ClockCost.sequence_reached_current source leafFlag compactAndLengths 0 (pathLength.toNat/2+24) (price source rfl) (by
    intro current run
    obtain ⟨⟨next⟩,frame⟩:=after_flag source current node tag buffer pathLength limit property data run
    have codes:=Input.LocalEffects.code_of_erase source current frame
    exact compact_phase_cost current node tag buffer pathLength limit property next fits (by rw [codes]; exact installed))
  simpa only [Nat.zero_add,leafFlag] using cost

theorem after_allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : CompactData (bind source "isl" 0#64) node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterAllocation).2.clock≤pathLength.toNat/2+24 := by
  rw [path_shapes.2.2.1]
  exact Input.ClockCost.declared_current source "isl" (.const 0#64) 0#64 afterLeafFlag _ rfl
    (after_leaf_flag_cost (bind source "isl" 0#64) node tag buffer pathLength limit property data fits installed)

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.CompactData.bind_leaf
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.leaf_flag_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_flag
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_leaf_flag_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_allocation_cost
