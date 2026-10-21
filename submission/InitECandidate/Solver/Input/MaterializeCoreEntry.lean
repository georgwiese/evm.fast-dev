import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.Mpt.WitnessCoreEntryTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Genuine original240/239 wrapper execution supplies the actual original
238 entry with the same physical databases, scratch cursor and hash runtime.
All wrapper outcomes retain a fixed overhead around that real child run. -/
theorem core_entry_of_materialize (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessMaterialize.body=(outcome,post)) :
    source.clock-post.clock≤5 ∨ ∃ entry target childResult,
      RootBoundary input entry ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      OriginalCode.Installed entry.code ∧ OriginalScalarGlobals.Scalars entry.globals ∧
      entry.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ entry.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      Rlp.Validation.Arena entry 2713714688#64 2701135872#64 ∧ Keccak256.Environment entry 2713714976#64 2713715176#64 ∧
      entry.clock=source.clock-3 ∧ evaluateHOLFiniteState entry Mpt.WitnessCore.body=(childResult,target) ∧ source.clock-post.clock≤entry.clock-target.clock+6 := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,dbCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
  rcases Mpt.WitnessMaterialize.core_trace source post nodes pointer length 2713714688#64 installed dbCell pCell nCell scratch.cursorGlobal outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨entry,target,childResult,pure,clock,dbEntry,pEntry,nEntry,childRun,allowance⟩ := reached
    have data:=RootBoundary.erase_frame input source entry originalBoundary pure (dbEntry.trans dbCell.symm)
    have frame:=runtime_of_entry source entry pure
    have entryInstalled : OriginalCode.Installed entry.code := by rw [frame.code]; exact installed
    have globals:=congrArg PanSemStateFiniteExact.globals pure
    change entry.globals=source.globals at globals
    have entryScalars : OriginalScalarGlobals.Scalars entry.globals := by rw [globals]; exact scalars
    exact Or.inr ⟨entry,target,childResult,data,pure,entryInstalled,entryScalars,pEntry,nEntry,
      frame.scratch source entry _ _ scratch,frame.hash_environment source entry _ _ environment,clock,childRun,allowance⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_entry_of_materialize
