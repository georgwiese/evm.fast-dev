import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.Headers.CurrentValidate.Allocation

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Normal return forces both genuine original allocations to succeed.
Their room and paid call clocks follow from that execution. -/
theorem entry_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    count.toNat≤256 ∧ 2≤source.clock ∧ heap.toNat+(hsSize count).toNat≤2952790016 ∧
      (hashesPointer heap count).toNat+(hashesSize count).toNat≤2952790016 ∧
      ∃ inner,evaluateHOLFiniteState (loopEntry source heap count) loops=(some (.returned value),inner) ∧ post=restoreEntry source heap count inner := by
  obtain ⟨small,remaining⟩ := count_returned source post count countCell value normal
  rw [shapes.2.1] at remaining
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [hsAmount]=some (PersistentAlloc.values (hsSize count)) := by
    simp [hsAmount,hsSize,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,countCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  obtain ⟨firstRoom,funded,middle,continued,endpoint⟩ := PersistentAlloc.call_normal source post "hs" [hsAmount] afterHs heap (hsSize count) args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapGlobal heapBound value remaining
  let first:=hsSource source heap count
  change evaluateHOLFiniteState first afterHs=(some (.returned value),middle) at continued
  have firstCount : first.locals.lookup (ofString "n")=some (.val (.word count)) :=
    (bind_lookup_other _ "hs" "n" _ (by decide)).trans countCell
  have firstHeap : first.globals.lookup (ofString "heap_ptr")=some (.val (.word (hashesPointer heap count))) := by
    simp [first,hsSource,hashesPointer,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,HolFiniteMapExact.lookup_update,FUPDATE]
  have firstBound : (hashesPointer heap count).toNat≤2952790016 := (PersistentAlloc.guards heap (hsSize count) firstRoom).2.2.2.1
  have firstInstalled : Input.OriginalCode.Installed first.code := installed
  rw [shapes.2.2.1] at continued
  have nextArgs : evalListHOLFinite first (h:=fun query=>Classical.propDecidable (first.memaddrs query)) [hashesAmount]=some (PersistentAlloc.values (hashesSize count)) := by
    simp [hashesAmount,hashesSize,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,firstCount,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  obtain ⟨secondRoom,nextFunded,final,rest,restored⟩ := PersistentAlloc.call_normal first middle "hashes" [hashesAmount] afterHashes (hashesPointer heap count) (hashesSize count) nextArgs
    (PersistentAlloc.original_code first.code firstInstalled) (Input.Trap.original_code first.code firstInstalled) firstHeap firstBound value continued
  change evaluateHOLFiniteState (hashesSource source heap count) afterHashes=(some (.returned value),final) at rest
  rw [loop_declaration] at rest
  let inner:=(evaluateHOLFiniteState (loopEntry source heap count) loops).2
  have actualResult:=congrArg Prod.fst rest
  have loopRun : evaluateHOLFiniteState (loopEntry source heap count) loops=(some (.returned value),inner) := Prod.ext actualResult rfl
  have finalEq : final=restore (hashesSource source heap count) "i" inner := (congrArg Prod.snd rest).symm
  have enough : 2≤source.clock := by change 1≤source.clock-1 at nextFunded; omega
  exact ⟨small,enough,firstRoom,secondRoom,inner,loopRun,by rw [endpoint,restored,finalEq]; rfl⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.entry_returned
