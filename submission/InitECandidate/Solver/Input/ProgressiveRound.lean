import InitECandidate.Solver.Input.CurrentHash.ProgressiveEntry
import InitECandidate.Solver.Input.ProgressiveUpdates
import InitECandidate.Solver.Input.MerkleCallHeap

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real current progressive bindings and retained original SHA environment.
This predicate contains neither a future execution nor a cost premise. -/
structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p")=some (.val (.word p))
  rootsLocal : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))
  position : source.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (offset k))))
  sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 (4^k))))
  round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))
  workspace : ShaPair.Workspace source stp accel

structure Geometry (p roots cursor zeros : BitVec 64) (n : Nat) : Prop where
  inputArena : AllocatedBytes.Arena p (32*n)
  rootsArena : AllocatedBytes.Arena roots 768
  temporary : AllocatedBytes.Arena cursor (64*n+32)
  aligned : cursor.toNat%8=0
  tableArena : AllocatedBytes.Arena zeros 2048

theorem RoundState.pair (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (actual : RoundState source p roots cursor zeros stp accel n k) :
    RoundState (pairEntry source n (offset k) (4^k)) p roots cursor zeros stp accel n k := by
  have frame := (pair_entry_frame source n (offset k) (4^k)).1
  have code : (pairEntry source n (offset k) (4^k)).code=source.code := by have h:=congrArg PanSemStateFiniteExact.code frame; exact h
  have domain : (pairEntry source n (offset k) (4^k)).memaddrs=source.memaddrs := by have h:=congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have globals : (pairEntry source n (offset k) (4^k)).globals=source.globals := by have h:=congrArg PanSemStateFiniteExact.globals frame; exact h
  exact ⟨(pair_entry_other source n (offset k) (4^k) "p" (by decide)).trans actual.pointer,
    (pair_entry_other source n (offset k) (4^k) "roots" (by decide)).trans actual.rootsLocal,
    (pair_entry_other source n (offset k) (4^k) "n" (by decide)).trans actual.count,
    (pair_entry_other source n (offset k) (4^k) "off" (by decide)).trans actual.position,
    (pair_entry_other source n (offset k) (4^k) "size" (by decide)).trans actual.sizeLocal,
    (pair_entry_other source n (offset k) (4^k) "k" (by decide)).trans actual.round,
    by rw [globals]; exact actual.heap,by rw [globals]; exact actual.table,
    ShaPair.Workspace.of_fields source _ stp accel actual.workspace code domain (by rw [globals]) (by rw [globals])⟩

theorem RoundState.dec_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (actual : RoundState source p roots cursor zeros stp accel n k) : RoundState (decClockHOLFinite source) p roots cursor zeros stp accel n k :=
  ⟨actual.pointer,actual.rootsLocal,actual.count,actual.position,actual.sizeLocal,actual.round,actual.heap,actual.table,
    ShaPair.Workspace.of_fields source _ stp accel actual.workspace rfl rfl rfl rfl⟩

/-- Current original call operands are physical subranges of the current
input/root arenas; the temporary bound follows from the actual chunk count. -/
theorem pair_geometry (p roots cursor zeros : BitVec 64) (n k : Nat) (bounded : n≤134217728) (active : offset k<n)
    (mapped : Geometry p roots cursor zeros n) :
    AllocatedBytes.Arena (p+BitVec.ofNat 64 (32*offset k)) (32*(min (4^k) (n-offset k))) ∧
    AllocatedBytes.Arena (roots+BitVec.ofNat 64 (32*k)) 32 ∧
    AllocatedBytes.Arena cursor (32*max 1 (2*(min (4^k) (n-offset k)))) := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  have a := Nat.min_le_left (4^k) (n-offset k)
  have b := Nat.min_le_right (4^k) (n-offset k)
  exact ⟨AllocatedBytes.Arena.subrange p (32*n) (32*offset k) (32*min (4^k) (n-offset k)) mapped.inputArena (by omega),
    AllocatedBytes.Arena.subrange roots 768 (32*k) 32 mapped.rootsArena (by omega),
    AllocatedBytes.Arena.weaken cursor (64*n+32) _ mapped.temporary (by omega)⟩

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_frame
#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_other
#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_count
#print axioms InitECandidate.Solver.Input.Progressive.RoundState.pair
#print axioms InitECandidate.Solver.Input.Progressive.RoundState.dec_clock
#print axioms InitECandidate.Solver.Input.Progressive.pair_geometry
