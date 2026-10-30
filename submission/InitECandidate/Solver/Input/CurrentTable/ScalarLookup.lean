import InitECandidate.Solver.Input.CurrentTable.NewScalarImage
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Empty
import InitECandidate.Solver.Input.CurrentTable.Get.Call

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def scalarBitsEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : BitVec 64) :=
  bind source "keybits" (key*8#64)
def scalarNodesEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key base : BitVec 64) :=
  bind (scalarBitsEntry source key) "nodes" base
def scalarRootEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key base root : BitVec 64) :=
  bind (scalarNodesEntry source key base) "n" root
def scalarRestoreEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key base : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "keybits" (restore (scalarBitsEntry source key) "nodes" (restore (scalarNodesEntry source key base) "n" post))

/-- The actual header loads and key-bit multiplication at arbitrary key
width, retaining the original traversal and all three declaration scopes. -/
theorem scalar_setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key base root : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.memory table=.word key) (nodesCell : source.memory (table+40#64)=.word base)
    (rootCell : source.memory (table+56#64)=.word root) :
    evaluateHOLFiniteState source body=
      let output:=evaluateHOLFiniteState (scalarRootEntry source key base root) afterRoot
      (output.1,scalarRestoreEntry source key base output.2) := by
  have keyRead:=header_read source table key 0 domain arena aligned (by decide) (by decide) tableCell (by simpa only [BitVec.add_zero] using keyCell)
  have bitsRead : eval source (.panop .mul [.load .one (tableAddress 0),.const 8#64])=some (.val (.word (key*8#64))) := by
    simp only [eval] at keyRead
    simp only [eval]
    rw [evalHOLExact]
    simp only [evalListHOLExact,keyRead]
    rfl
  have firstTable : (scalarBitsEntry source key).locals.lookup (ofString "t")=some (.val (.word table)) :=
    (bind_lookup_other source "keybits" "t" (key*8#64) (by decide)).trans tableCell
  have nodesRead:=header_read (scalarBitsEntry source key) table base 40 domain arena aligned (by decide) (by decide) firstTable nodesCell
  have secondTable : (scalarNodesEntry source key base).locals.lookup (ofString "t")=some (.val (.word table)) :=
    (bind_lookup_other (scalarBitsEntry source key) "nodes" "t" base (by decide)).trans firstTable
  have rootRead:=header_read (scalarNodesEntry source key base) table root 56 domain arena aligned (by decide) (by decide) secondTable rootCell
  let output:=evaluateHOLFiniteState (scalarRootEntry source key base root) afterRoot
  have last : evaluateHOLFiniteState (scalarNodesEntry source key base) afterNodes=
      (output.1,restore (scalarNodesEntry source key base) "n" output.2) := by
    rw [body_shapes.2.2.1]
    exact ScalarScope.declare_execute _ _ "n" (.load .one (tableAddress 56)) root afterRoot output.1 rootRead rfl
  have middle : evaluateHOLFiniteState (scalarBitsEntry source key) afterBits=
      (output.1,restore (scalarBitsEntry source key) "nodes" (restore (scalarNodesEntry source key base) "n" output.2)) := by
    rw [body_shapes.2.1]
    exact ScalarScope.declare_execute _ _ "nodes" (.load .one (tableAddress 40)) base afterNodes output.1 nodesRead last
  rw [body_shapes.1]
  exact ScalarScope.declare_execute source _ "keybits" (.panop .mul [.load .one (tableAddress 0),.const 8#64]) (key*8#64) afterBits output.1 bitsRead middle

/-- An actual empty scalar table returns zero at every body clock,
without reading a key byte or any uninitialized backing-array word. -/
theorem body_scalar_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64)
    (image : New.ScalarEmpty source table key cap)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    (evaluateHOLFiniteState source body).1=some (.returned (.val (.word 0#64))) ∧
    (evaluateHOLFiniteState source body).2.clock=source.clock ∧
    LocalEffects.erase (evaluateHOLFiniteState source body).2=LocalEffects.erase source := by
  have keyCell : source.memory table=.word key:=by
    simpa only [BitVec.add_zero] using image.fields (table+0#64,key) (by simp [New.scalarWrites])
  have nodesCell:=image.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.scalarWrites])
  have rootCell:=image.fields (table+56#64,0#64) (by simp [New.scalarWrites])
  let ready:=scalarRootEntry source key (New.scalarNodesPointer table key cap) 0#64
  have nodeCell : ready.locals.lookup (ofString "n")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have loopRun:=empty_loop ready nodeCell
  have afterRun : evaluateHOLFiniteState ready afterRoot=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite ready) := by
    rw [body_shapes.2.2.2,evaluateHOLFiniteState_seq_line780,loopRun]
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,nodeCell,shapeOfHOLExact]
  rw [scalar_setup_execute source table key (New.scalarNodesPointer table key cap) 0#64 image.domain image.geometry.table image.aligned tableCell keyCell nodesCell rootCell,afterRun]
  exact ⟨rfl,rfl,rfl⟩

/-- Every actual empty-table scoped lookup either stops within one source
tick or resumes its genuine continuation with zero and the complete frame. -/
theorem scoped_scalar_empty_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap pointer : BitVec 64) (image : New.ScalarEmpty source table key cap)
    (installed : OriginalCode.Installed source.code) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") arguments continuation)=(outcome,post)) :
    (source.clock-post.clock≤1 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target inner,
      LocalEffects.erase target=LocalEffects.erase source ∧ target.clock=source.clock-1 ∧
      source.clock-target.clock≤1 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word 0#64))) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩:=word_pair_environment source.code.lookup (ofString "htab_find_leaf") (ofString "t") (ofString "key")
    body .one table pointer (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have currentImage : New.ScalarEmpty entry table key cap:=image.of_erase rfl
  obtain ⟨answer,clock,physical⟩:=body_scalar_empty entry table key cap currentImage tableCell
  have price : entry.clock-(evaluateHOLFiniteState entry body).2.clock≤0:=by rw [clock]; omega
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_find_leaf") arguments _ body continuation callee .one 0 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    rw [bodyRun] at answer clock physical
    have valueEq : value=.val (.word 0#64):=by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using answer
    rw [valueEq] at continued
    exact Or.inr ⟨target,inner,physical,clock,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Whole current empty lookup: one source call tick, a literal absent
normal result, and a full nonlocal frame at arbitrary runtime key width. -/
theorem body_scalar_empty (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap pointer : BitVec 64) (image : New.ScalarEmpty source table key cap)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1 ∧ LocalEffects.erase post=LocalEffects.erase source ∧
      ∀ value,outcome=some (.returned value) → value=absentValue ∧ post.clock=source.clock-1 := by
  have physical:=body_readonly source.code installed source rfl
  rw [run] at physical
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) lookupArguments=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,tableCell,keyCell]
  rw [body_shape] at run
  rcases FindLeaf.scoped_scalar_empty_trace source post table key cap pointer image installed "leaf" lookupArguments afterLeaf args outcome run with stopped|reached
  · exact ⟨stopped.1,physical,by intro value same; exact (stopped.2 value same).elim⟩
  · obtain ⟨target,inner,frame,clock,cost,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 0#64))
    have leafCell:=CallNormal.continuation_lookup_same source target "leaf" (.val (.word 0#64))
    change evaluateHOLFiniteState current afterLeaf=(outcome,inner) at continued
    rw [after_leaf_empty current leafCell] at continued
    have expected : evaluateHOLFiniteState current absent=(some (.returned absentValue),emptyLocalsHOLFinite current):=by
      simp [absent,absentValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [expected] at continued
    have resultEq:=congrArg Prod.fst continued
    have innerEq:=congrArg Prod.snd continued
    dsimp only at resultEq innerEq
    have postClock : post.clock=target.clock:=by rw [endpoint,←innerEq]; rfl
    refine ⟨by rw [postClock]; exact cost,physical,?_⟩
    intro value normal
    have valueEq : value=absentValue:=by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (resultEq.trans normal).symm
    exact ⟨valueEq,postClock.trans clock⟩

theorem call_scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap pointer : BitVec 64) (image : New.ScalarEmpty source table key cap)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htab_get") arguments)).2.clock≤2 := by
  obtain ⟨callee,called,tableCell,keyCell⟩:=word_pair_environment source.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    body resultShape table pointer (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have priced:=body_scalar_empty entry (evaluateHOLFiniteState entry body).2 table key cap pointer (image.of_erase rfl)
    tableCell keyCell installed (evaluateHOLFiniteState entry body).1 rfl
  exact ClockCost.call_current source destination (ofString "htab_get") arguments _ body callee resultShape 1 args called priced.1

/-- The real original get caller retains the exact absent result and all
physical memory. The incoming key pointer is unrestricted. -/
theorem scoped_scalar_empty_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap pointer : BitVec 64) (image : New.ScalarEmpty source table key cap)
    (installed : OriginalCode.Installed source.code) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "htab_get") arguments continuation)=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target inner,
      LocalEffects.erase target=LocalEffects.erase source ∧ target.clock≤source.clock ∧ source.clock-target.clock≤2 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name absentValue) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩:=word_pair_environment source.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    body resultShape table pointer (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have currentImage : New.ScalarEmpty entry table key cap:=image.of_erase rfl
  have priced:=body_scalar_empty entry (evaluateHOLFiniteState entry body).2 table key cap pointer currentImage tableCell keyCell installed (evaluateHOLFiniteState entry body).1 rfl
  rcases CallNormal.scoped_classified source post name resultShape (ofString "htab_get") arguments _ body continuation callee resultShape 1 args called priced.1 outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨price,physical,answer⟩:=body_scalar_empty entry target table key cap pointer currentImage tableCell keyCell installed _ bodyRun
    obtain ⟨valueEq,clock⟩:=answer value rfl
    rw [valueEq] at continued
    exact Or.inr ⟨target,inner,physical,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scalar_setup_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_scalar_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_scalar_empty_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.body_scalar_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.call_scalar_empty_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.scoped_scalar_empty_trace
