import InitECandidate.Solver.Mpt.NodeRlpBeginFooter
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  bind (bind (bind (bind source "k" 3#64) "payload" 0#64) "cbuf" 0#64) "clen" 0#64

theorem branch_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64))) :
    evaluateHOLFiniteState source pathChoice=(none,source) := by
  rw [body_shapes.2.2.2.2.2,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

theorem branch_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (branchEntry source).locals.lookup (ofString "k")=some (.val (.word 3#64)) ∧
      (branchEntry source).locals.lookup (ofString "payload")=some (.val (.word 0#64)) ∧
      (branchEntry source).locals.lookup (ofString "cbuf")=some (.val (.word 0#64)) ∧
      (branchEntry source).locals.lookup (ofString "clen")=some (.val (.word 0#64)) ∧
      (branchEntry source).locals.lookup (ofString "fr")=source.locals.lookup (ofString "fr") := by
  simp [branchEntry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

/-- A real branch begin spends no source ticks on every outcome. Its
actual mapped tag is read before selecting the skipped compact-path phase. -/
theorem branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tagRead : eval source (nodeField 0)=some (.val (.word 3#64))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤0 := by
  let entered:=branchEntry source
  have selected:=branch_choice entered (branch_entry_cells source).1
  have suffix : entered.clock-(evaluateHOLFiniteState entered afterLength).2.clock≤0:=by
    rw [body_shapes.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,selected]
    exact footer_cost entered.code entered rfl
  rw [body_shapes.1]
  apply Input.ClockCost.declared_current source "k" (nodeField 0) 3#64 afterTag 0 tagRead
  rw [body_shapes.2.1]
  apply Input.ClockCost.declared_current _ "payload" (.const 0#64) 0#64 afterPayload 0 rfl
  rw [body_shapes.2.2.1]
  apply Input.ClockCost.declared_current _ "cbuf" (.const 0#64) 0#64 afterBuffer 0 rfl
  rw [body_shapes.2.2.2.1]
  exact Input.ClockCost.declared_current _ "clen" (.const 0#64) 0#64 afterLength 0 rfl suffix

/-- The actual original branch begin initializes its three frame fields
to zero. Mapping, source-clock preservation and exact memory writes are
derived from execution, including every lexical restoration. -/
theorem branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (tagRead : eval source (nodeField 0)=some (.val (.word 3#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=storedMemory source.memory frame 0#64 0#64 0#64} ∧
      source.memaddrs (frame+24#64) ∧ source.memaddrs (frame+32#64) ∧ source.memaddrs (frame+40#64) := by
  have shaped:=normal
  rw [body_shapes.1] at shaped
  obtain ⟨first,firstRun,firstEnd⟩:=Input.declaration_return_word source target "k" (nodeField 0) 3#64 afterTag value tagRead shaped
  rw [body_shapes.2.1] at firstRun
  obtain ⟨second,secondRun,secondEnd⟩:=Input.declaration_return_word _ first "payload" (.const 0#64) 0#64 afterPayload value rfl firstRun
  rw [body_shapes.2.2.1] at secondRun
  obtain ⟨third,thirdRun,thirdEnd⟩:=Input.declaration_return_word _ second "cbuf" (.const 0#64) 0#64 afterBuffer value rfl secondRun
  rw [body_shapes.2.2.2.1] at thirdRun
  obtain ⟨fourth,fourthRun,fourthEnd⟩:=Input.declaration_return_word _ third "clen" (.const 0#64) 0#64 afterLength value rfl thirdRun
  change evaluateHOLFiniteState (branchEntry source) afterLength=(some (.returned value),fourth) at fourthRun
  rw [body_shapes.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,branch_choice (branchEntry source) (branch_entry_cells source).1] at fourthRun
  have enteredCells:=branch_entry_cells source
  obtain ⟨answer,endpoint,firstMapped,secondMapped,thirdMapped⟩:=footer_normal (branchEntry source) fourth frame 0#64 0#64 0#64
    (enteredCells.2.2.2.2.trans frameCell) enteredCells.2.2.1 enteredCells.2.2.2.1 enteredCells.2.1 value fourthRun
  refine ⟨answer,?_,firstMapped,secondMapped,thirdMapped⟩
  rw [firstEnd,secondEnd,thirdEnd,fourthEnd,endpoint]
  rfl

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_choice
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_entry_cells
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_normal
