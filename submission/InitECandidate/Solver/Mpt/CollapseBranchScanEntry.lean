import InitECandidate.Solver.Mpt.CollapseBranchScanNormal
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def setup (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "count" 0#64) "idx" 0#64) "i" 0#64

def initial_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) : ScanModel (setup source) node := by
  refine ⟨0#64,0#64,0#64,?_,?_,?_,?_,by decide,by decide,by decide,?_,?_⟩
  · simpa [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using nodeCell
  · simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · intro impossible; exact (impossible rfl).elim
  · intro impossible; exact (impossible rfl).elim

theorem normal_setup (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner,target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧
      evaluateHOLFiniteState (setup source) afterCounter=(some (.returned value),inner) := by
  rw [setup_shapes.1] at normal
  obtain ⟨first,firstRun,firstEq⟩:=Input.declaration_return_word source target "count" (.const 0#64) 0#64 afterCount value rfl normal
  rw [setup_shapes.2.1] at firstRun
  obtain ⟨second,secondRun,secondEq⟩:=Input.declaration_return_word (QueryBranch.bind source "count" 0#64) first "idx" (.const 0#64) 0#64 afterIndex value rfl firstRun
  rw [setup_shapes.2.2.1] at secondRun
  obtain ⟨inner,continued,innerEq⟩:=Input.declaration_return_word (QueryBranch.bind (QueryBranch.bind source "count" 0#64) "idx" 0#64) second "i" (.const 0#64) 0#64 afterCounter value rfl secondRun
  refine ⟨inner,?_,?_,continued⟩
  · rw [firstEq,secondEq,innerEq]; rfl
  · rw [firstEq,secondEq,innerEq]; rfl

/-- The original collapse entry initializes all three counters and then
really scans the sixteen child slots. The model and actual suffix are
derived from normal execution, together with every lexical scope frame. -/
theorem scan_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (children : ∀ index<16,∃ child : BitVec 64,source.memaddrs (node+32#64+BitVec.ofNat 64 index*8#64) ∧
      source.memory (node+32#64+BitVec.ofNat 64 index*8#64)=.word child)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ scannedState inner,∃ finished : ScanModel scannedState node,
      evaluateHOLFiniteState (setup source) scan=(none,scannedState) ∧ finished.index.toNat=16 ∧
      Input.LocalEffects.erase scannedState=Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState scannedState afterScan=(some (.returned value),inner) ∧
      target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner := by
  obtain ⟨inner,clock,frame,continued⟩:=normal_setup source target value normal
  rw [setup_shapes.2.2.2] at continued
  have safe : Input.LocalPrefix (ofString "node") scan:=by
    rw [scan_shapes.1]
    exact .loop scanTest (scan_body_safe _ (by decide) (by decide) (by decide))
  obtain ⟨scannedState,scanRun,tailRun⟩:=Input.sequence_returned (setup source) inner scan afterScan value
    (fun returned=>(safe.summary_full (setup source)).2.1 returned) continued
  obtain ⟨preserved,finished,stopped⟩:=scan_normal (setup source) scannedState node (initial_model source node nodeCell) children scanRun
  exact ⟨scannedState,inner,finished,scanRun,stopped,preserved,tailRun,clock,frame⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.initial_model
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.normal_setup
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_entry
