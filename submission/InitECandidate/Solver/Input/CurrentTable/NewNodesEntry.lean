import InitECandidate.Solver.Input.CurrentTable.NewArraysProgram

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def keysPointer (heap : BitVec 64) : BitVec 64 := PersistentAlloc.rounded heap 88#64
def nodesEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) :=
  arrayEntry (keysEntry source heap cap) heap (keysPointer heap) (size32 cap) "keys" 32

def restoreKeys (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restorePrefix source heap (restore (keysEntry source heap cap) "keys" target)

/-- The actual keys allocation follows the real header prefix. Its room is
derived at that same call; all previous stops are bounded explicitly. -/
theorem nodes_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤3 ∧ ∀ value,outcome≠some (.returned value)) ∨ 2≤source.clock ∧ heap.toNat+88≤2952790016 ∧
      (keysPointer heap).toNat+(size32 cap).toNat≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      ∃ inner,evaluateHOLFiniteState (nodesEntry source heap cap) nodesCall=(outcome,inner) ∧ post=restoreKeys source heap cap inner := by
  rcases keys_trace source post heap cap keyLocal capLocal atLeastTwo heapCell heapLower heapBound heapAligned domain installed outcome run with stopped|reached
  · exact Or.inl ⟨by have h:=stopped.1; omega,stopped.2⟩
  · obtain ⟨funded,firstRoom,arena,middle,continued,endpoint⟩:=reached
    have headerFrame:=keys_frame source heap cap arena
    have bound : (keysPointer heap).toNat≤2952790016 := (PersistentAlloc.guards heap 88#64 firstRoom).2.2.2.1
    obtain ⟨tableCell,keyCell,strideCell,capCell⟩:=fields_cells source heap cap keyLocal capLocal
    have ncapCell : (keysEntry source heap cap).locals.lookup (ofString "ncap")=some (.val (.word cap)) := bind_lookup_same _ _ _
    have args:=keys_arguments (keysEntry source heap cap) cap ncapCell strideCell
    rw [array_shapes.1] at continued
    rcases array_allocation_trace (keysEntry source heap cap) middle heap (keysPointer heap) (size32 cap) "keys" 32 [keyAmount] nodesCall
      (by decide) (by decide) (by decide) domain arena heapAligned tableCell args installed headerFrame.1 bound outcome continued with stopped|allocated
    · have clock : post.clock=middle.clock := by rw [endpoint]; rfl
      have price:=stopped.1
      change source.clock-1-middle.clock≤2 at price
      exact Or.inl ⟨by rw [clock]; omega,stopped.2⟩
    · obtain ⟨nextFunded,room,inner,rest,restored⟩:=allocated
      have positive : 2≤source.clock := by change 1≤source.clock-1 at nextFunded; omega
      exact Or.inr ⟨positive,firstRoom,room,arena,inner,rest,by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.nodes_trace
