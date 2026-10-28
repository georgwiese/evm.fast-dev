import InitECandidate.Solver.Input.CurrentTable.NodeBuild.PriorImage

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The complete earlier database contract survives a later actual builder,
including its physical image and original input/global frame. -/
theorem Returned.after_builder {data priorData : Data}
    {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap priorTable priorCap : BitVec 64}
    (previous : Returned priorData origin source priorTable priorCap)
    (later : Returned data source post table cap)
    (lower : data.lower≤priorData.lower) (tableLower : data.lower≤priorTable.toNat)
    (before : (New.endPointer priorTable priorCap).toNat≤data.upper) :
    Returned priorData origin post priorTable priorCap := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,countBound⟩ := previous.image
  have oldGeometry : New.Geometry priorTable priorCap := image.geometry
  have geometry (gTable gCap : BitVec 64) (g : New.Geometry gTable gCap) : gTable.toNat+88≤(New.endPointer gTable gCap).toNat := by
    have a:=g.tableBefore
    have b:=g.keysBefore
    have c:=g.nodesBefore
    have d:=g.orderBefore
    omega
  have oldEnd := geometry priorTable priorCap oldGeometry
  have oldUpper : priorData.upper≤data.upper := by have := previous.tableAfter; omega
  have installed := later.arena.code
  have environment : CurrentKeccak.Hash.Environment post priorData.stp priorData.pad :=
    ⟨installed,later.arena.domain,(later.globals _ (by decide)).trans previous.environment.stateGlobal,
      (later.globals _ (by decide)).trans previous.environment.padGlobal,
      previous.environment.stateArena,previous.environment.padArena,previous.environment.stateAligned,previous.environment.padAligned⟩
  obtain ⟨newRoot,newNext,newCount,newValid,newBits,newLeft,newRight,newKeys,newImage,newCountBound⟩ := later.image
  have newGeometry : New.Geometry table cap := newImage.geometry
  have newEnd := geometry table cap newGeometry
  obtain ⟨heap,heapCell,heapLower,heapUpper,heapAligned⟩ := later.heap
  have heap : NormalHeapEffects.AtLeast (New.endPointer priorTable priorCap).toNat post :=
    ⟨heap,heapCell,by have := later.tableAfter; omega,heapUpper,heapAligned⟩
  have nextImage := later.prior_image image previous.little tableLower before
  exact ⟨later.arena,later.little,environment,(later.globals _ (by decide)).trans previous.outCell,heap,
    ⟨by intro query low high; exact (later.input.words query (by omega) (by omega)).trans (previous.input.words query low high)⟩,
    (fun key different=>(later.globals key different).trans (previous.globals key different)),
    ⟨root,next,count,valid,bits,left,right,keys,nextImage,countBound⟩,previous.tableAfter,previous.totalBound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned.after_builder
