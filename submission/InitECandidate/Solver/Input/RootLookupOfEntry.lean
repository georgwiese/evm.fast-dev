import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.Mpt.WitnessDecodeRootTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Genuine root comparison carries both immutable databases and runtime
to the actual lookup boundary. All early comparison outcomes keep their cost. -/
theorem root_lookup_of_entry (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body=(outcome,post)) :
    source.clock-post.clock≤129 ∨ ∃ current inner,
      RootBoundary input current ∧ LocalEffects.erase current=LocalEffects.erase source ∧
      OriginalCode.Installed current.code ∧ OriginalScalarGlobals.Scalars current.globals ∧
      current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧ Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤129 ∧
      evaluateHOLFiniteState current Mpt.WitnessDecodeRoot.lookupCall=(outcome,inner) ∧ post=QueryBranch.restore source "is_empty" inner := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
  obtain ⟨emptyRoot,emptyCell⟩ := scalars _ OriginalScalarGlobals.mpt_names.1
  rcases Mpt.WitnessDecodeRoot.lookup_trace source post nodes root emptyRoot installed nodeCell rootCell emptyCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,pure,forward,spent,dbCurrent,rootCurrent,continued,endpoint⟩ := reached
    have data:=RootBoundary.erase_frame input source current originalBoundary pure (dbCurrent.trans nodeCell.symm)
    have frame:=runtime_of_entry source current pure
    have currentInstalled : OriginalCode.Installed current.code := by rw [frame.code]; exact installed
    have globals:=congrArg PanSemStateFiniteExact.globals pure
    change current.globals=source.globals at globals
    have currentScalars : OriginalScalarGlobals.Scalars current.globals := by rw [globals]; exact scalars
    exact Or.inr ⟨current,inner,data,pure,currentInstalled,currentScalars,rootCurrent,
      frame.scratch source current _ _ scratch,frame.hash_environment source current _ _ environment,forward,spent,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_lookup_of_entry
