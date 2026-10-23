import InitECandidate.Solver.Mpt.NodeRlpBeginEntry

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def start (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64) :=
  bind (bind (bind (bind source "k" tag) "payload" 0#64) "cbuf" 0#64) "clen" 0#64

def Entry.start (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap tag : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property) :
    Entry (start source tag) node heap lower limit property :={
  graph:=data.graph
  member:=data.member
  active:=data.active
  nonHash:=data.nonHash
  values:=data.values
  regions:=data.regions
  heapCell:=data.heapCell
  heapLower:=data.heapLower
  heapUpper:=data.heapUpper
  heapAligned:=data.heapAligned
  domain:=data.domain }

theorem start_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64) :
    (start source tag).locals.lookup (ofString "k")=some (.val (.word tag)) ∧
      (start source tag).locals.lookup (ofString "payload")=some (.val (.word 0#64)) ∧
      (start source tag).locals.lookup (ofString "cbuf")=some (.val (.word 0#64)) ∧
      (start source tag).locals.lookup (ofString "clen")=some (.val (.word 0#64)) ∧
      (start source tag).locals.lookup (ofString "node")=source.locals.lookup (ofString "node") ∧
      (start source tag).locals.lookup (ofString "fr")=source.locals.lookup (ofString "fr") := by
  simp [start,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

def bodyAllowance (memory : BitVec 64→HolWordLab 64) (node : BitVec 64) : Nat:=
  if wordAt memory node=3#64 then 0 else (wordAt memory (node+40#64)).toNat/2+26

theorem tag_cases (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property) :
    wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64 ∨ wordAt source.memory node=3#64 := by
  have bounded:=data.graph.kindBound node data.member data.active
  have positive : (wordAt source.memory node).toNat≠0:=by
    intro zero
    exact data.nonHash (BitVec.eq_of_toNat_eq zero)
  have cases : (wordAt source.memory node).toNat=1 ∨ (wordAt source.memory node).toNat=2 ∨ (wordAt source.memory node).toNat=3:=by omega
  rcases cases with first|second|third
  · exact Or.inl (BitVec.eq_of_toNat_eq first)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq second))
  · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq third))

theorem path_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap oldBuffer : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word oldBuffer))) :
    source.clock-(evaluateHOLFiniteState source pathChoice).2.clock≤bodyAllowance source.memory node := by
  have selected : evaluateHOLFiniteState source pathChoice=
      if wordAt source.memory node=3#64 then (none,source) else evaluateHOLFiniteState source pathScope:=by
    rw [body_shapes.2.2.2.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [selected,bodyAllowance]
  by_cases branch : wordAt source.memory node=3#64
  · simp only [if_pos branch]
    simp
  · simp only [if_neg branch]
    have pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by
      rcases tag_cases source node heap lower limit property data with leaf|extension|other
      · exact Or.inl leaf
      · exact Or.inr extension
      · exact (branch other).elim
    exact path_scope_cost source node heap oldBuffer lower limit property data pathTag valueFits installed nodeCell tagCell bufferCell

/-- Whole unchanged original257 begin is bounded on every outcome from
its actual registered non-hash node and current persistent heap. Branches
spend zero body ticks; leaves/extensions spend at most floor(path/2)+26. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyAllowance source.memory node := by
  let entered:=start source (wordAt source.memory node)
  let currentData:=data.start source node heap (wordAt source.memory node) lower limit property
  have cells:=start_cells source (wordAt source.memory node)
  have front:= path_choice_cost entered node heap 0#64 lower limit property currentData valueFits installed (cells.2.2.2.2.1.trans nodeCell) cells.1 cells.2.2.1
  have suffix:=Input.ClockCost.sequence_current entered pathChoice footer (bodyAllowance source.memory node) 0 front (footer_cost source.code)
  rw [body_shapes.1]
  apply Input.ClockCost.declared_current source "k" (nodeField 0) (wordAt source.memory node) afterTag _ (tag_read source node heap lower limit property data nodeCell)
  rw [body_shapes.2.1]
  apply Input.ClockCost.declared_current _ "payload" (.const 0#64) 0#64 afterPayload _ rfl
  rw [body_shapes.2.2.1]
  apply Input.ClockCost.declared_current _ "cbuf" (.const 0#64) 0#64 afterBuffer _ rfl
  rw [body_shapes.2.2.2.1]
  apply Input.ClockCost.declared_current _ "clen" (.const 0#64) 0#64 afterLength _ rfl
  rw [body_shapes.2.2.2.2.1]
  exact suffix

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.start
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.start_cells
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.tag_cases
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_choice_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.body_cost
