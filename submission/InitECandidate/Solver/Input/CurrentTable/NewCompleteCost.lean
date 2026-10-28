import InitECandidate.Solver.Input.CurrentTable.NewFinalStores

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same caller bindings survive all three actual array scopes. -/
theorem final_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) :
    (finalEntry source heap cap).locals.lookup (ofString "t")=some (.val (.word heap)) ∧
    (finalEntry source heap cap).locals.lookup (ofString "ncap")=some (.val (.word cap)) := by
  have first:=array_frame (keysEntry source heap cap) heap (keysPointer heap) (size32 cap) "keys" 32
  have second:=array_frame (nodesEntry source heap cap) heap (nodesPointer heap cap) (size32 cap) "nodes" 40
  have third:=array_frame (orderEntry source heap cap) heap (orderPointer heap cap) (size8 cap) "order" 48
  have tableBefore:=(fields_cells source heap cap keyLocal capLocal).1
  have ncapBefore : (keysEntry source heap cap).locals.lookup (ofString "ncap")=some (.val (.word cap)) := bind_lookup_same _ _ _
  exact ⟨(third.2.2.1 (ofString "t") (by decide)).trans ((second.2.2.1 (ofString "t") (by decide)).trans ((first.2.2.1 (ofString "t") (by decide)).trans tableBefore)),
    (third.2.2.1 (ofString "ncap") (by decide)).trans ((second.2.2.1 (ofString "ncap") (by decide)).trans ((first.2.2.1 (ofString "ncap") (by decide)).trans ncapBefore))⟩

/-- The actual32-byte-key Patricia constructor costs at most five source
ticks from a reached current entry. Four successful allocations spend four;
any failed allocation stops with at most one additional trap tick. All
array room and normal metadata stores are derived along the actual run. -/
theorem current_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤5 := by
  let output:=evaluateHOLFiniteState source body
  rcases final_trace source output.2 heap cap keyLocal capLocal atLeastTwo heapCell heapLower heapBound heapAligned domain installed output.1 rfl with stopped|reached
  · exact stopped.1
  · obtain ⟨funded,firstRoom,keysRoom,nodesRoom,orderRoom,arena,inner,continued,endpoint⟩:=reached
    obtain ⟨tableCell,ncapCell⟩:=final_cells source heap cap keyLocal capLocal
    have finish:=final_fields_execute (finalEntry source heap cap) heap cap domain arena heapAligned tableCell ncapCell
    rw [finish] at continued
    have innerEq:=congrArg Prod.snd continued
    dsimp only at innerEq
    have clock : output.2.clock=source.clock-4 := by
      rw [endpoint,←innerEq]
      change source.clock-1-1-1-1=source.clock-4
      omega
    change source.clock-output.2.clock≤5
    rw [clock]
    omega

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.final_cells
#print axioms InitECandidate.Solver.Input.CurrentTable.New.current_body_cost
