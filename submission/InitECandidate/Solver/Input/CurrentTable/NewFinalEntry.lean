import InitECandidate.Solver.Input.CurrentTable.NewOrderEntry

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def orderPointer (heap cap : BitVec 64) : BitVec 64 := PersistentAlloc.rounded (nodesPointer heap cap) (size32 cap)
def finalEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) :=
  arrayEntry (orderEntry source heap cap) heap (orderPointer heap cap) (size8 cap) "order" 48

def restoreOrder (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restoreNodes source heap cap (restore (orderEntry source heap cap) "order" target)

theorem order_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cap : BitVec 64)
    (ncapCell : source.locals.lookup (ofString "ncap")=some (.val (.word cap))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [orderAmount]=some (PersistentAlloc.values (size8 cap)) := by
  simp [orderAmount,size8,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
    ncapCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

/-- The last actual array allocation derives its own request room, and
all four paid allocation calls are retained. Earlier allocation failures
stop within five source ticks on every outcome. -/
theorem final_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤5 ∧ ∀ value,outcome≠some (.returned value)) ∨ 4≤source.clock ∧ heap.toNat+88≤2952790016 ∧
      (keysPointer heap).toNat+(size32 cap).toNat≤2952790016 ∧
      (nodesPointer heap cap).toNat+(size32 cap).toNat≤2952790016 ∧
      (orderPointer heap cap).toNat+(size8 cap).toNat≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      ∃ inner,evaluateHOLFiniteState (finalEntry source heap cap) finalFields=(outcome,inner) ∧ post=restoreOrder source heap cap inner := by
  rcases order_trace source post heap cap keyLocal capLocal atLeastTwo heapCell heapLower heapBound heapAligned domain installed outcome run with stopped|reached
  · exact Or.inl ⟨by have h:=stopped.1; omega,stopped.2⟩
  · obtain ⟨funded,firstRoom,keysRoom,nodesRoom,arena,middle,continued,endpoint⟩:=reached
    have firstFrame:=array_frame (keysEntry source heap cap) heap (keysPointer heap) (size32 cap) "keys" 32
    have frame:=array_frame (nodesEntry source heap cap) heap (nodesPointer heap cap) (size32 cap) "nodes" 40
    have bound : (orderPointer heap cap).toNat≤2952790016 := (PersistentAlloc.guards (nodesPointer heap cap) (size32 cap) nodesRoom).2.2.2.1
    have tableBefore:=(fields_cells source heap cap keyLocal capLocal).1
    have tableCell : (orderEntry source heap cap).locals.lookup (ofString "t")=some (.val (.word heap)) :=
      (frame.2.2.1 (ofString "t") (by decide)).trans ((firstFrame.2.2.1 (ofString "t") (by decide)).trans tableBefore)
    have ncapBefore : (keysEntry source heap cap).locals.lookup (ofString "ncap")=some (.val (.word cap)) := bind_lookup_same _ _ _
    have ncapCell : (orderEntry source heap cap).locals.lookup (ofString "ncap")=some (.val (.word cap)) :=
      (frame.2.2.1 (ofString "ncap") (by decide)).trans ((firstFrame.2.2.1 (ofString "ncap") (by decide)).trans ncapBefore)
    have args:=order_arguments (orderEntry source heap cap) cap ncapCell
    rw [array_shapes.2.2] at continued
    rcases array_allocation_trace (orderEntry source heap cap) middle heap (orderPointer heap cap) (size8 cap) "order" 48 [orderAmount] finalFields
      (by decide) (by decide) (by decide) domain arena heapAligned tableCell args installed frame.1 bound outcome continued with stopped|allocated
    · have clock : post.clock=middle.clock := by rw [endpoint]; rfl
      have price:=stopped.1
      change source.clock-1-1-1-middle.clock≤2 at price
      exact Or.inl ⟨by rw [clock]; omega,stopped.2⟩
    · obtain ⟨nextFunded,room,inner,rest,restored⟩:=allocated
      have positive : 4≤source.clock := by change 1≤source.clock-1-1-1 at nextFunded; omega
      exact Or.inr ⟨positive,firstRoom,keysRoom,nodesRoom,room,arena,inner,rest,by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.order_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.New.final_trace
