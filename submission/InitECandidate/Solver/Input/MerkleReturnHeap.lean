import InitECandidate.Solver.Input.HeapCopyRelease
import InitECandidate.Solver.Input.MerkleGlobals
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal output suffix executes the original release with the
saved mark. Normality derives its funding; no successful release is assumed. -/
theorem output_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [extension_shape.2.2.2] at run
  exact HeapScope.copy_release_return_heap source post mark old outputArguments installed saved heap value run

/-- Dense and extension loops preserve their actual heap/mark; the real
normal suffix then restores the saved cursor. This says nothing about
cryptographic output contents. -/
theorem dense_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dn : Nat) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source denseContinuation=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [outer_shape.2.2] at run
  obtain ⟨halved,halvedRun,remaining⟩ := sequence_returned source post outerLoop afterDense value
    ((outer_loop_other (ofString "mark") (by decide) (by decide) (by decide)).summary_full source).2.1 run
  have halvedOther (name : String) (a : ofString name≠ofString "cur") (b : ofString name≠ofString "half") (c : ofString name≠ofString "j") :
      halved.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (outer_loop_other (ofString name) a b c).summary_full source
    unfold LocalSummary at summary
    rw [halvedRun] at summary
    exact summary.1 rfl
  have halvedGlobal := outer_loop_globals (ofString "heap_ptr") source.code installed source rfl
  rw [halvedRun] at halvedGlobal
  have halvedHeap := (congrArg Prod.snd halvedGlobal).trans heap
  have fields := evaluation_fields source halved outerLoop none halvedRun
  have halvedInstalled : OriginalCode.Installed halved.code := fields.2.2.2.symm ▸ installed
  have read : eval halved (localVar "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using (halvedOther "dn" (by decide) (by decide) (by decide)).trans depth
  rw [extension_shape.1] at remaining
  obtain ⟨inner,innerRun,endpoint⟩ := declaration_return_word halved post "d" (localVar "dn") (BitVec.ofNat 64 dn) _ value read remaining
  let entry := bind halved "d" (BitVec.ofNat 64 dn)
  obtain ⟨extended,extensionRun,outputRun⟩ := sequence_returned entry inner extensionLoop afterExtension value
    ((extension_loop_other (ofString "mark") (by decide)).summary_full entry).2.1 innerRun
  have extensionLocals := (extension_loop_other (ofString "mark") (by decide)).summary_full entry
  unfold LocalSummary at extensionLocals
  rw [extensionRun] at extensionLocals
  have entryMark : entry.locals.lookup (ofString "mark")=some (.val (.word mark)) :=
    (bind_lookup_other halved "d" "mark" (BitVec.ofNat 64 dn) (by decide)).trans ((halvedOther "mark" (by decide) (by decide) (by decide)).trans saved)
  have extendedMark := (extensionLocals.1 rfl).trans entryMark
  have extensionGlobals := extension_loop_globals (ofString "heap_ptr") entry.code halvedInstalled entry rfl
  rw [extensionRun] at extensionGlobals
  have extendedHeap := (congrArg Prod.snd extensionGlobals).trans halvedHeap
  have nextFields := evaluation_fields entry extended extensionLoop none extensionRun
  have extendedInstalled : OriginalCode.Installed extended.code := nextFields.2.2.2.symm ▸ halvedInstalled
  have restored := output_return_heap extended inner mark old extendedInstalled extendedMark extendedHeap value outputRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.output_return_heap
#print axioms InitECandidate.Solver.Input.Merkle.dense_return_heap
