import InitECandidate.Solver.Mpt.InsertNodeChoiceOutput
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def iterationRestore (source post : PanSemStateFiniteExact 64 Guest.HostMemory):=
  restore source "r" (restore (QueryBranch.bind source "r" 0#64) "next_node"
    (restore (QueryBranch.bind (QueryBranch.bind source "r" 0#64) "next_node" 0#64) "next_slot"
      (restore (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "r" 0#64) "next_node" 0#64) "next_slot" 0#64) "next_level" post)))

theorem iteration_scope_shape : loopBody=.dec (ofString "r") .one (.const 0#64)
    (.dec (ofString "next_node") .one (.const 0#64) (.dec (ofString "next_slot") .one (.const 0#64)
      (.dec (ofString "next_level") .one (.const 0#64) (.seq clearGo (.seq nodeChoice afterChoice))))) := by
  rw [iteration_shape]
  rfl

/-- Invert the four genuine local declarations and original go-clear,
then expose the actual dispatch and footer, with exact scope restoration. -/
theorem iteration_entry_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ chosen finished,evaluateHOLFiniteState (dispatchEntry source) nodeChoice=(none,chosen) ∧
      evaluateHOLFiniteState chosen afterChoice=(none,finished) ∧ target=iterationRestore source finished := by
  rw [iteration_scope_shape] at normal
  obtain ⟨first,run1,end1⟩:=Input.declaration_none_word source target "r" (.const 0#64) 0#64 _ rfl normal
  let one:=QueryBranch.bind source "r" 0#64
  obtain ⟨second,run2,end2⟩:=Input.declaration_none_word one first "next_node" (.const 0#64) 0#64 _ rfl run1
  let two:=QueryBranch.bind one "next_node" 0#64
  obtain ⟨third,run3,end3⟩:=Input.declaration_none_word two second "next_slot" (.const 0#64) 0#64 _ rfl run2
  let three:=QueryBranch.bind two "next_slot" 0#64
  obtain ⟨fourth,run4,end4⟩:=Input.declaration_none_word three third "next_level" (.const 0#64) 0#64 _ rfl run3
  obtain ⟨cleared,goRun,continued⟩:=Input.sequence_none (prepared source) fourth clearGo (.seq nodeChoice afterChoice) run4
  have clearedEq : cleared=dispatchEntry source:=Input.assign_none (prepared source) cleared "go" (.const 0#64) 0#64 rfl goRun
  subst cleared
  obtain ⟨chosen,choiceRun,footerRun⟩:=Input.sequence_none (dispatchEntry source) fourth nodeChoice afterChoice continued
  refine ⟨chosen,fourth,choiceRun,footerRun,?_⟩
  rw [end1,end2,end3,end4]
  rfl

theorem iteration_restore_lookup (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notRoot : ofString name≠ofString "r") (notNode : ofString name≠ofString "next_node")
    (notSlot : ofString name≠ofString "next_slot") (notLevel : ofString name≠ofString "next_level") :
    (iterationRestore source post).locals.lookup (ofString name)=post.locals.lookup (ofString name) := by
  unfold iterationRestore
  rw [restore_lookup_other source _ "r" name notRoot,restore_lookup_other _ _ "next_node" name notNode,
    restore_lookup_other _ _ "next_slot" name notSlot,restore_lookup_other _ _ "next_level" name notLevel]

theorem iteration_restore_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (iterationRestore source post).clock=post.clock ∧ Input.LocalEffects.erase (iterationRestore source post)=Input.LocalEffects.erase post := ⟨rfl,rfl⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.iteration_scope_shape
#print axioms InitECandidate.Solver.Mpt.Insert.iteration_entry_normal
#print axioms InitECandidate.Solver.Mpt.Insert.iteration_restore_lookup
#print axioms InitECandidate.Solver.Mpt.Insert.iteration_restore_frame
