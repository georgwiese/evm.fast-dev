import InitECandidate.Solver.WitnessRadix.PopBody
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.WitnessRadix.PopProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure StoreSafe (destination depth pendingStart pendingCount pendingNode parent : BitVec 64) : Prop where
  startAway : pendingStart + (depth - 1#64) * 8#64 ≠ destination
  countAway : pendingCount + (depth - 1#64) * 8#64 ≠ destination
  parentAway : pendingNode + (depth - 1#64) * 8#64 ≠ destination
  bitAway : parent ≠ destination

theorem cells_of_fields {F : Type} {source target : PanSemStateFiniteExact 64 F}
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    {depth pendingStart pendingCount pendingNode start count parent bit : BitVec 64}
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit) :
    Cells target depth pendingStart pendingCount pendingNode start count parent bit := by
  rcases cells with ⟨a,b,c,d,e,f,g,h⟩
  rw [memory] at b d f h
  rw [domain] at a c e g
  exact ⟨a,b,c,d,e,f,g,h⟩

theorem locals_of_field {F : Type} {source target : PanSemStateFiniteExact 64 F}
    (field : source.locals = target.locals)
    {depth start count bit dest pendingStart pendingCount pendingNode : BitVec 64}
    (locals : Locals source depth start count bit dest pendingStart pendingCount pendingNode) :
    Locals target depth start count bit dest pendingStart pendingCount pendingNode := by
  rcases locals with ⟨a,b,c,d,e,f,g,h⟩
  rw [field] at a b c d e f g h
  exact ⟨a,b,c,d,e,f,g,h⟩

theorem cells_store {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth pendingStart pendingCount pendingNode start count parent bit destination value : BitVec 64)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit)
    (safe : StoreSafe destination depth pendingStart pendingCount pendingNode parent) :
    Cells { source with memory := StoreWord.put source.memory destination value }
      depth pendingStart pendingCount pendingNode start count parent bit := by
  refine ⟨cells.startMapped, ?_, cells.countMapped, ?_, cells.parentMapped, ?_, cells.bitMapped, ?_⟩
  · simpa only [StoreWord.put, if_neg safe.startAway] using cells.startWord
  · simpa only [StoreWord.put, if_neg safe.countAway] using cells.countWord
  · simpa only [StoreWord.put, if_neg safe.parentAway] using cells.parentWord
  · simpa only [StoreWord.put, if_neg safe.bitAway] using cells.bitWord

theorem locals_ordinal {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth start count bit dest pendingStart pendingCount pendingNode ordinal : BitVec 64)
    (locals : Locals source depth start count bit dest pendingStart pendingCount pendingNode) :
    Locals (bind source "ordinal" ordinal) depth start count bit dest pendingStart pendingCount pendingNode := by
  have unchanged (name : String) (neq : ofString "ordinal" ≠ ofString name) :=
    bind_lookup_other source "ordinal" name ordinal neq
  exact ⟨(unchanged _ (by decide)).trans locals.depthLocal,
    (unchanged _ (by decide)).trans locals.startLocal,
    (unchanged _ (by decide)).trans locals.countLocal,
    (unchanged _ (by decide)).trans locals.bitLocal,
    (unchanged _ (by decide)).trans locals.destLocal,
    (unchanged _ (by decide)).trans locals.pendingStartLocal,
    (unchanged _ (by decide)).trans locals.pendingCountLocal,
    (unchanged _ (by decide)).trans locals.pendingNodeLocal⟩

theorem restore_pop_ordinal {F : Type} (saved state : PanSemStateFiniteExact 64 F)
    (depth start count parent bit : BitVec 64) :
    restore saved "ordinal" (popPost state depth start count parent bit) =
      popPost (restore saved "ordinal" state) depth start count parent bit := by
  unfold popPost
  rw [restore_bind_other saved _ "ordinal" "dest" _ (by decide),
    restore_bind_other saved _ "ordinal" "bit" _ (by decide),
    restore_bind_other saved _ "ordinal" "count" _ (by decide),
    restore_bind_other saved _ "ordinal" "start" _ (by decide),
    restore_bind_other saved _ "ordinal" "depth" _ (by decide)]

end InitECandidate.Solver.WitnessRadix.PopProgram

#print axioms InitECandidate.Solver.WitnessRadix.PopProgram.cells_store
