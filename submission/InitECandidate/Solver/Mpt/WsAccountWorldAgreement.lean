import InitECandidate.Solver.Mpt.WsAccountWorld
import InitECandidate.Solver.MutableTable.FamilyFloorFrame
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Reconstruct the actual witness graph and value fields from agreement
on exactly their current footprint. No next graph/model is a premise. -/
def World.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (worldGlobal : target.globals.lookup (ofString "ws")=source.globals.lookup (ofString "ws"))
    (scratchGlobal : target.globals.lookup (ofString "mpt_nib_scratch")=source.globals.lookup (ofString "mpt_nib_scratch"))
    (agree : ∀ query,world.graph.Footprint query ∨ TrieWalk.ValueFootprint world.graph query ∨ query=ws+24#64 → target.memory query=source.memory query) :
    World target ws root nibs cutoff frozenEnd valueLimit := by
  let graph := TrieWalk.Graph.of_agreement source.memory target.memory source.memaddrs target.memaddrs world.graph domain
    (fun query needed=>agree query (Or.inl needed))
  have validEq : graph.valid=world.graph.valid := rfl
  have tags : ∀ node,world.graph.valid node → node≠0#64 → GasBudget.wordAt target.memory node=GasBudget.wordAt source.memory node := by
    intro node member active
    unfold GasBudget.wordAt
    rw [agree node (Or.inl (.header node member active))]
  refine {
    graph := graph
    member := by rw [validEq]; exact world.member
    values := TrieWalk.Values.of_agreement source.memory target.memory source.memaddrs target.memaddrs world.graph graph valueLimit world.values validEq domain tags
      (fun query needed=>agree query (Or.inr (Or.inl needed)))
    worldState := worldGlobal.trans world.worldState
    rootMapped := by rw [domain]; exact world.rootMapped
    rootStored := (agree _ (Or.inr (Or.inr rfl))).trans world.rootStored
    scratch := scratchGlobal.trans world.scratch
    domain := domain.trans world.domain
    little := endian.trans world.little
    nibsArena := world.nibsArena
    nibsBelow := world.nibsBelow
    ordered := world.ordered
    bounded := world.bounded
    footprint := ?_ }
  intro query needed
  rcases needed with structureWord | valueWord | rootWord
  · exact world.footprint query (Or.inl (TrieWalk.Graph.footprint_transport source.memory target.memory source.memaddrs target.memaddrs world.graph graph validEq tags query structureWord))
  · exact world.footprint query (Or.inr (Or.inl (TrieWalk.ValueFootprint.transport source.memory target.memory source.memaddrs target.memaddrs world.graph graph validEq tags query valueWord)))
  · exact world.footprint query (Or.inr (Or.inr rootWord))

/-- Actual table-family mutations retain immutable witness ownership from
their derived lifetime-floor frame. Heap growth and table relocation are
allowed; current witness bytes are reconstructed, never assumed afterward. -/
def World.after_family {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit)
    (objects next : ι → MutableTable.TableFamily.Object)
    (frame : MutableTable.TableFamily.FloorFrame objects next source target) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) (globals : HeapGlobals source target) :
    World target ws root nibs cutoff frozenEnd valueLimit :=
  World.of_agreement source target ws root nibs cutoff frozenEnd valueLimit world domain endian
    (globals _ (by decide)) (globals _ (by decide))
    (fun query needed=>frame.below frozenEnd floors query (world.footprint query needed).2)

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.of_agreement
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.after_family
