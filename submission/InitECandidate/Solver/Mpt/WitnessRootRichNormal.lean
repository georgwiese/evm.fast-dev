import InitECandidate.Solver.Mpt.WitnessRootMaterializeNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors Input.Main.WitnessConstructors WitnessMaterialize WitnessCore

/-- The actual empty return has an empty closed registry at the genuine
incoming heap, while retaining both constructed witness databases. -/
theorem empty_rich_output (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    RichOutput input heap.toNat db source (.val (.word 0#64)) := by
  have frozen:=boundary.freeze input source heap heapCell
  have actualBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualHeapCell,arena,aligned,nodeBefore,codeBefore⟩:=actualBoundary
  have same : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualHeapCell.symm.trans heapCell)))
  subst actualHeap
  have named:=frozen.frame input source (QueryBranch.bind source "db" db) heap.toNat rfl rfl ((bind_lookup_same source "db" db).trans dbCell.symm) (by intros; rfl)
  exact ⟨⟨heap,0#64,rfl,heapCell,arena,aligned,Nat.le_refl _,⟨cursor,cursorCell⟩,named,Or.inl rfl⟩,
    heap,0#64,rfl,heapCell,NodeRegistry.empty source heap.toNat heap db,(NodeRegistry.empty source heap.toNat heap db).graph.null⟩

/-- Whole original241: every actual normal return carries the exact
materialized node in a bounded closed physical graph with bounded values.
The root buffer arena is actual caller data; no future success or
input-graph acyclicity assumption is needed. -/
theorem rich_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap root emptyRoot : BitVec 64) (boundary : RootBoundary input source)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64) (rootArena : AllocatedBytes.Arena root 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    RichOutput input heap.toNat db post returned := by
  rcases prefix_normal source post db root emptyRoot installed dbCell rootCell emptyCell returned normal with empty|lookup
  · obtain ⟨returnedEq,pure⟩:=empty
    rw [returnedEq]
    exact (empty_rich_output input source db heap 2713714688#64 boundary dbCell heapCell scratch.cursorGlobal).of_erase
      input heap.toNat db source post (.val (.word 0#64)) pure
  · obtain ⟨lookupSource,lookupPost,lookupPure,lookupDb,lookupRoot,lookupRun,endpoint⟩:=lookup
    have lookupBoundary:=boundary.erase_frame input source lookupSource lookupPure (lookupDb.trans dbCell.symm)
    have lookupFrame:=runtime_of_entry source lookupSource lookupPure
    have lookupInstalled : Input.OriginalCode.Installed lookupSource.code:=by rw [lookupFrame.code]; exact installed
    obtain ⟨caller,answer,inner,callerPure,callerDb,callerRoot,callerR,hit,continued,lookupEnd⟩:=
      lookup_normal input lookupSource lookupPost db root lookupBoundary lookupInstalled lookupDb lookupRoot returned lookupRun
    have wholePure:=callerPure.trans lookupPure
    have callerBoundary:=boundary.erase_frame input source caller wholePure (callerDb.trans dbCell.symm)
    have callerFrame:=runtime_of_entry source caller wholePure
    have callerInstalled : Input.OriginalCode.Installed caller.code:=by rw [callerFrame.code]; exact installed
    have globals:=congrArg PanSemStateFiniteExact.globals wholePure
    change caller.globals=source.globals at globals
    have callerHeap : caller.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have callerScratch:=callerFrame.scratch source caller 2713714688#64 2701135872#64 scratch
    have output:=after_lookup_rich_normal input caller inner db heap root answer callerBoundary callerInstalled callerDb callerRoot callerR callerHeap heapLower callerScratch rootArena
      (by intro slice present; obtain ⟨index,inside,sliceEq,small,arena,lower,before⟩:=hit slice present; exact ⟨small,lower,before⟩) returned continued
    apply output.of_erase input heap.toNat db inner post returned
    rw [endpoint,lookupEnd]; rfl

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.empty_rich_output
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.rich_body_normal
