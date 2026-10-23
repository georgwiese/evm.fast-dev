import InitECandidate.Solver.Mpt.DeleteExtensionSimple
import InitECandidate.Solver.Mpt.TrieGraphKinds
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tag_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner,evaluateHOLFiniteState (QueryBranch.bind source "ck" (wordAt source.memory child)) afterTag=(some (.returned value),inner) ∧
      target=restore source "ck" inner := by
  have reached:=nonnull_entry source target child childCell active value normal
  obtain ⟨mapped,stored⟩:=graph.header child member active
  have read : eval source (field "nc" 0#64)=some (.val (.word (wordAt source.memory child))):=by
    simp [eval,field,localVar,evalHOLExact,evalListHOLExact,toExact,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  rw [entry_shapes.2.2.1] at reached
  exact Input.declaration_return_word source target "ck" (field "nc" 0#64) _ afterTag value read reached

/-- The real branch guard selects a stopping pointer-update return or
the unchanged merge suffix on every outcome. -/
theorem branch_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) :
    evaluateHOLFiniteState source afterTag=if tag=3#64 then evaluateHOLFiniteState source branchFinish else evaluateHOLFiniteState source afterBranch := by
  have read : evaluateHOLFiniteState source branchGuard=if tag=3#64 then evaluateHOLFiniteState source branchFinish else (none,source):=by
    rw [entry_shapes.2.2.2.2,evaluateHOLFiniteState_ite]
    by_cases selected : tag=3#64 <;>
      simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,selected,evaluateHOLFiniteState_skip]
  have stops : Input.NoFallthrough branchFinish:=by
    rw [branchFinish]
    exact .sequence _ _ (.returned _)
  rw [entry_shapes.2.2.2.1]
  exact Input.sequence_choice source branchGuard branchFinish afterBranch (tag=3#64) read stops

theorem hash_guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source hashGuard=(none,target)) : target=source ∧ tag≠0#64 := by
  by_cases zero : tag=0#64
  · have selected : evaluateHOLFiniteState source hashGuard=evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]):=by
      rw [merge_shapes.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact (Fail.call_not_normal source target installed _ (selected.symm.trans normal)).elim
  · have skipped : evaluateHOLFiniteState source hashGuard=(none,source):=by
      rw [merge_shapes.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    exact ⟨congrArg Prod.snd (normal.symm.trans skipped),zero⟩

/-- A genuine normal merge observes an initialized leaf or extension.
The failing hash case and the stopping branch case cannot supply a future
successful concatenation premise. -/
theorem merge_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (notBranch : wordAt source.memory child≠3#64) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterTag=(some (.returned value),target)) :
    (wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64) ∧
      evaluateHOLFiniteState source concatScope=(some (.returned value),target) := by
  rw [branch_dispatch source _ tagCell,if_neg notBranch,merge_shapes.1] at normal
  have safe : Input.LocalPrefix (ofString "nc") hashGuard:=by
    rw [merge_shapes.2.1]
    exact .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,guardRun,continued⟩:=Input.sequence_returned source target hashGuard concatScope value
    (fun returned=>(safe.summary_full source).2.1 returned) normal
  obtain ⟨same,notHash⟩:=hash_guard_normal source middle _ tagCell installed guardRun
  subst middle
  exact ⟨graph.path_kind child member active notHash notBranch,continued⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.tag_entry
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.branch_dispatch
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.hash_guard_normal
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.merge_entry
