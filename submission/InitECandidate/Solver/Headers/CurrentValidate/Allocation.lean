import InitECandidate.Solver.Headers.CurrentValidate.Count
import InitECandidate.Solver.Input.CurrentAllocationTrace
import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def hsSize (count : BitVec 64) := count*8#64+8#64
def hashesSize (count : BitVec 64) := count*32#64+32#64
def hsSource (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (hsSize count)) "hs" heap
def hashesPointer (heap count : BitVec 64) := PersistentAlloc.rounded heap (hsSize count)
def hashesSource (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) :=
  let first:=hsSource source heap count
  bind (PersistentAlloc.post {first with clock:=first.clock-1} (hashesPointer heap count) (hashesSize count)) "hashes" (hashesPointer heap count)
def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) := bind (hashesSource source heap count) "i" 0#64
def restoreEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "hs" (restore (hsSource source heap count) "hashes" (restore (hashesSource source heap count) "i" target))

theorem size_numbers (count : BitVec 64) (small : count.toNat≤256) :
    (hsSize count).toNat=8*count.toNat+8 ∧ (hashesSize count).toNat=32*count.toNat+32 := by
  constructor
  · simp [hsSize,BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_eq_of_lt (show count.toNat*8<2^64 by omega),Nat.mod_eq_of_lt (show count.toNat*8+8<2^64 by omega)]
    omega
  · simp [hashesSize,BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_eq_of_lt (show count.toNat*32<2^64 by omega),Nat.mod_eq_of_lt (show count.toNat*32+32<2^64 by omega)]
    omega

theorem loop_declaration (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evaluateHOLFiniteState source afterHashes=
      (let output:=evaluateHOLFiniteState (bind source "i" 0#64) loops;(output.1,restore source "i" output.2)) := by
  rw [shapes.2.2.2.1]
  exact Input.ScalarScope.declare_execute source _ "i" (.const 0#64) 0#64 loops _ rfl rfl

/-- The real validator guard and two original allocations either stop
within four source ticks or reach its actual first loop with derived room,
two paid caller clocks and all original lexical restorations. -/
theorem entry_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (installed : Input.OriginalCode.Installed source.code)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    source.clock-post.clock≤4 ∨ count.toNat≤256 ∧ 2≤source.clock ∧
      heap.toNat+(hsSize count).toNat≤2952790016 ∧
      (hashesPointer heap count).toNat+(hashesSize count).toNat≤2952790016 ∧
      ∃ inner,evaluateHOLFiniteState (loopEntry source heap count) loops=(result,inner) ∧ post=restoreEntry source heap count inner := by
  rcases count_trace source post count countCell result run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨small,remaining⟩ := reached
    rw [shapes.2.1] at remaining
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [hsAmount]=some (PersistentAlloc.values (hsSize count)) := by
      simp [hsAmount,hsSize,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,countCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
    rcases Input.CurrentAlloc.scoped_trace source post "hs" [hsAmount] afterHs heap (hsSize count) args installed heapGlobal heapBound result remaining with stopped|allocated
    · exact Or.inl (by omega)
    · obtain ⟨funded,room,middle,continued,endpoint⟩ := allocated
      let first:=hsSource source heap count
      change evaluateHOLFiniteState first afterHs=(result,middle) at continued
      have firstCount : first.locals.lookup (ofString "n")=some (.val (.word count)) :=
        (bind_lookup_other _ "hs" "n" _ (by decide)).trans countCell
      have firstHeap : first.globals.lookup (ofString "heap_ptr")=some (.val (.word (hashesPointer heap count))) := by
        simp [first,hsSource,hashesPointer,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,HolFiniteMapExact.lookup_update,FUPDATE]
      have firstBound : (hashesPointer heap count).toNat≤2952790016 := (PersistentAlloc.guards heap (hsSize count) room).2.2.2.1
      have firstInstalled : Input.OriginalCode.Installed first.code := installed
      rw [shapes.2.2.1] at continued
      have nextArgs : evalListHOLFinite first (h:=fun query=>Classical.propDecidable (first.memaddrs query)) [hashesAmount]=some (PersistentAlloc.values (hashesSize count)) := by
        simp [hashesAmount,hashesSize,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,firstCount,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
      rcases Input.CurrentAlloc.scoped_trace first middle "hashes" [hashesAmount] afterHashes (hashesPointer heap count) (hashesSize count) nextArgs firstInstalled firstHeap firstBound result continued with stopped|allocated
      · have finalClock : post.clock=middle.clock := by rw [endpoint]; rfl
        change source.clock-1-middle.clock≤2 at stopped
        rw [finalClock]
        exact Or.inl (by omega)
      · obtain ⟨nextFunded,nextRoom,final,rest,restored⟩ := allocated
        change evaluateHOLFiniteState (hashesSource source heap count) afterHashes=(result,final) at rest
        rw [loop_declaration] at rest
        let inner:=(evaluateHOLFiniteState (loopEntry source heap count) loops).2
        have actualResult:=congrArg Prod.fst rest
        have loopRun : evaluateHOLFiniteState (loopEntry source heap count) loops=(result,inner) := Prod.ext actualResult rfl
        have finalEq : final=restore (hashesSource source heap count) "i" inner := (congrArg Prod.snd rest).symm
        have enough : 2≤source.clock := by change 1≤source.clock-1 at nextFunded; omega
        exact Or.inr ⟨small,enough,room,nextRoom,inner,loopRun,by rw [endpoint,restored,finalEq]; rfl⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.size_numbers
#print axioms InitECandidate.Solver.Headers.CurrentValidate.loop_declaration
#print axioms InitECandidate.Solver.Headers.CurrentValidate.entry_trace
