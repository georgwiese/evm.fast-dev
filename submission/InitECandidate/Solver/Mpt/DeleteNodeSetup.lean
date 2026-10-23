import InitECandidate.Solver.Mpt.DeleteNodeProgram
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64):=QueryBranch.bind {source with clock:=source.clock-1} "mark" cursor
def scalarSetup (source : PanSemStateFiniteExact 64 Guest.HostMemory):=QueryBranch.bind (QueryBranch.bind source "e" 0#64) "res" 0#64

theorem mark_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (name : String)
    (other : ofString "mark"≠ofString name) : (marked source cursor).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor other

theorem scalar_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notError : ofString "e"≠ofString name) (notResult : ofString "res"≠ofString name) :
    (scalarSetup source).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "res" name 0#64 notResult).trans (bind_lookup_other source "e" name 0#64 notError)

/-- A genuinely returning wrapper first saves the actual current scratch
cursor. Its mark call is pure and supplies its real paid continuation. -/
theorem mark_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (value : ValueHOL 64)
    (stored : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    1≤source.clock ∧ ∃ inner,evaluateHOLFiniteState (marked source cursor) afterMark=(some (.returned value),inner) ∧ target=restore source "mark" inner := by
  rw [shapes.1] at normal
  have funded:=(Input.CallNormal.scoped_data source target "mark" .one (ofString "scratch_mark") [] afterMark value normal).1
  have actual:=Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) stored funded
  simp only [Arenas.markName] at actual
  rw [actual] at normal
  let output:=evaluateHOLFiniteState (marked source cursor) afterMark
  have resultEq:=congrArg Prod.fst normal
  have postEq:=congrArg Prod.snd normal
  exact ⟨funded,output.2,Prod.ext resultEq rfl,postEq.symm⟩

/-- Follow both actual scalar declarations and their genuine lexical
exits before exposing the original caught call/release/return core. -/
theorem scalar_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned value),target)) :
    ∃ inner,evaluateHOLFiniteState (scalarSetup source) afterResult=(some (.returned value),inner) ∧
      target=restore source "e" (restore (QueryBranch.bind source "e" 0#64) "res" inner) := by
  rw [shapes.2.1] at normal
  obtain ⟨errorInner,continued,endpoint⟩:=Input.declaration_return_word source target "e" (.const 0#64) 0#64 afterError value rfl normal
  rw [shapes.2.2.1] at continued
  obtain ⟨inner,run,errorEndpoint⟩:=Input.declaration_return_word (QueryBranch.bind source "e" 0#64) errorInner "res" (.const 0#64) 0#64 afterResult value rfl continued
  exact ⟨inner,run,endpoint.trans (congrArg (restore source "e") errorEndpoint)⟩

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.mark_saved
#print axioms InitECandidate.Solver.Mpt.DeleteNode.scalar_saved
#print axioms InitECandidate.Solver.Mpt.DeleteNode.mark_entry
#print axioms InitECandidate.Solver.Mpt.DeleteNode.scalar_entry
