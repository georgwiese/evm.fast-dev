import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionEntry
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selected_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node index child : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (mapped : source.memaddrs (node+32#64+index*8#64)) (stored : source.memory (node+32#64+index*8#64)=.word child) :
    eval source (.load .one (childAddress (localVar "idx")))=some (.val (.word child)) := by
  simp [eval,childAddress,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    memLoadHOLExact,isWfShapeExactHOL,←BitVec.add_assoc,mapped,stored]

/-- Actual saved-index selection and child/tag declarations. The index
and nonnull selected cell come from the completed original scan model;
the physical child closure comes from the current registered branch. -/
theorem child_entry_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node index : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index))) (bounded : index.toNat<16)
    (selectedNonzero : wordAt source.memory (node+32#64+index*8#64)≠0#64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source childScope=(some (.returned value),post)) :
    ∃ child inner,graph.valid child ∧ child≠0#64 ∧
      evaluateHOLFiniteState (QueryBranch.bind (QueryBranch.bind source "child" child) "ck" (wordAt source.memory child)) afterKind=(some (.returned value),inner) ∧
      post=restore source "child" (restore (QueryBranch.bind source "child" child) "ck" inner) := by
  let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) index.toNat bounded
  have product : BitVec.ofNat 64 (index.toNat*8)=index*8#64:=by rw [BitVec.ofNat_mul]; simp
  have mapped : source.memaddrs (node+32#64+index*8#64):=by simpa only [product] using view.mapped
  have stored : source.memory (node+32#64+index*8#64)=.word view.child:=by simpa only [product] using view.stored
  have number : wordAt source.memory (node+32#64+index*8#64)=view.child:=by simp [wordAt,stored,MemoryBytes.wordBits]
  have childActive : view.child≠0#64:=by rwa [number] at selectedNonzero
  have read:=selected_read source node index view.child nodeCell indexCell mapped stored
  rw [child_shapes.1] at normal
  obtain ⟨first,kindRun,firstEq⟩:=Input.declaration_return_word source post "child" (.load .one (childAddress (localVar "idx"))) view.child kindScope value read normal
  let selected:=QueryBranch.bind source "child" view.child
  have childCell : selected.locals.lookup (ofString "child")=some (.val (.word view.child)):=bind_lookup_same _ _ _
  obtain ⟨headerMapped,headerStored⟩:=graph.header view.child view.member childActive
  have tagRead : eval selected (field "child" 0#64)=some (.val (.word (wordAt source.memory view.child))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read selected "child" view.child 0#64 _ childCell
      (by simpa only [selected,QueryBranch.bind,setVarHOLFinite,BitVec.add_zero] using headerMapped) (by simpa only [selected,QueryBranch.bind,setVarHOLFinite,BitVec.add_zero] using headerStored)
  rw [child_shapes.2.1] at kindRun
  obtain ⟨inner,continued,innerEq⟩:=Input.declaration_return_word selected first "ck" (field "child" 0#64) (wordAt source.memory view.child) afterKind value tagRead kindRun
  exact ⟨view.child,inner,view.member,childActive,continued,by rw [firstEq,innerEq]⟩

/-- The literal hash guard is identical to the already checked original
extension-finish guard; a real normal guard must have skipped its failure. -/
theorem hash_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source hashGuard=(none,post)) : post=source ∧ tag≠0#64 := by
  rw [child_shapes.2.2.2.1,←DeleteExtension.merge_shapes.2.1] at normal
  exact DeleteExtension.hash_guard_normal source post tag tagCell installed normal

theorem after_kind_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterKind=(some (.returned value),post)) :
    tag≠0#64 ∧ evaluateHOLFiniteState source nibbleScope=(some (.returned value),post) := by
  have safe : Input.LocalPrefix (ofString "child") hashGuard:=by
    rw [child_shapes.2.2.2.1]
    exact .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  rw [child_shapes.2.2.1] at normal
  obtain ⟨middle,guardRun,continued⟩:=Input.sequence_returned source post hashGuard nibbleScope value
    (fun returned=>(safe.summary_full source).2.1 returned) normal
  obtain ⟨same,notHash⟩:=hash_guard_normal source middle tag tagCell installed guardRun
  subst middle
  exact ⟨notHash,continued⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.selected_read
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.child_entry_normal
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.hash_guard_normal
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_kind_entry
