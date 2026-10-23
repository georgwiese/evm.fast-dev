import InitECandidate.Solver.Mpt.DeleteUnwindModel

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Reconstruct the actual current unwind state after its checked choice.
Both real cursor globals and every remaining physical PREV record survive;
the returned root becomes the genuine current res value. -/
def UnwindModel.after_choice (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property)
    (output : ChoiceOutput source target model.graph model.heap limit nodeLower pathLower property) :
    UnwindModel target limit nodeLower pathLower property := {
  heap:=output.finalHeap
  cursor:=model.cursor
  frame:=model.frame
  top:=model.top
  result:=output.root
  frames:=model.frames
  topCell:=by
    rw [output.locals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "res"≠ofString "top" from by decide] using model.topCell
  resultCell:=by rw [output.locals]; simp [HolFiniteMapExact.update,FUPDATE]
  heapCell:=output.heapCell
  heapArena:=output.heapArena
  heapAligned:=output.heapAligned
  scratch:={
    domain:=output.domain.trans model.scratch.domain
    cursorGlobal:=(output.globals (ofString "scratch_ptr") (by decide)).trans model.scratch.cursorGlobal
    limitGlobal:=(output.globals (ofString "frame_mem_ptr") (by decide)).trans model.scratch.limitGlobal
    ordered:=model.scratch.ordered
    aligned:=model.scratch.aligned
    lower:=model.scratch.lower
    upper:=model.scratch.upper }
  scratchBefore:=model.scratchBefore
  floor:=model.floor
  pathFloor:=model.pathFloor
  nodeFloor:=model.nodeFloor.trans output.grows
  little:=output.endian.trans model.little
  installed:=by rw [output.code]; exact model.installed
  graph:=output.next
  resultMember:=output.rootMember
  values:=output.values
  regions:=output.regions
  disjoint:=output.disjoint
  paths:=output.paths
  pathRegions:=output.pathRegions
  separated:=output.separated
  stack:=model.stack.of_before source target model.cursor.toNat nodeLower model.top model.frames (model.floor.trans model.pathFloor) output.memory
  parents:=output.parents source target model.graph model.heap limit nodeLower pathLower property model.frames model.parents
  bounded:=model.bounded }

end InitECandidate.Solver.Mpt.DeleteBody
