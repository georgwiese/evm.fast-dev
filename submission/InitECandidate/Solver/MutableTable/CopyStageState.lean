import InitECandidate.Solver.MutableTable.CopyProgram
import InitECandidate.Solver.MutableTable.CopyUsedContents
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame
import InitECandidate.Solver.WitnessRadix.AllocationExpected

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (next : Plan) (pool : Pool) :=
  PersistentAlloc.nextState source (name pool) (next.base pool) (next.base pool + size kind next pool)
def copied {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :=
  CopyGeneral.callState (allocated source kind next pool) (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool)
def stageState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :=
  let post := copied source kind old next pool
  if pool = .header then post else {post with memory := StoreWord.put post.memory (cell next .header (headerOffset pool)) (cell next pool 0)}
def stagePrice (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) : Nat :=
  CopyGeneral.cost (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool) + 2
def stageMemory (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) : WordWrites.Memory :=
  let output := CopyGeneral.resultMemory input be (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool)
  if pool = .header then output else StoreWord.put output (cell next .header (headerOffset pool)) (cell next pool 0)

theorem stage_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :
    emptyLocalsHOLFinite (stageState source kind old next pool) = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool))))
      memory := stageMemory source.memory source.be kind old next pool
      clock := source.clock - stagePrice kind old next pool} := by
  have subtraction : source.clock - 1 - (CopyGeneral.cost (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool) + 1) =
      source.clock - stagePrice kind old next pool := by unfold stagePrice; omega
  simp only [stageState, copied, allocated, PersistentAlloc.nextState, CopyGeneral.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
    stageMemory, subtraction]
  split <;> rfl

theorem stage_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :
    (stageState source kind old next pool).clock = source.clock - stagePrice kind old next pool := by
  exact congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) (stage_frame source kind old next pool)

theorem stage_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :
    (stageState source kind old next pool).memory = stageMemory source.memory source.be kind old next pool := by
  exact congrArg (fun state : PanSemStateFiniteExact 64 F => state.memory) (stage_frame source kind old next pool)

/-- One real copy stage leaves every old table pool unchanged. Both the
copy destination and the rewritten new header are after the old pools. -/
theorem stage_preserves_old (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second) (pool : Pool) :
    MemoryModel.PoolFrame input (stageMemory input be kind old next pool) kind old := by
  have fits : amount kind old.capacity pool ≤ size kind next pool := by rw [← sameCapacity]; exact amount_room kind next pool
  intro oldPool offset inside
  have away : CopyGeneral.Away (cell next pool 0) (cell old oldPool offset) (amount kind old.capacity pool) := by
    rw [← region_pointer kind next pool]
    apply MemoryRegion.copy_away _ (MemoryRegion.pool_valid kind next nextValid pool) _ fits
    left
    rw [number kind old oldValid oldPool offset inside]
    have ordered := earlier oldPool pool
    change old.base oldPool + offset < next.base pool
    omega
  have copied := CopyGeneral.resultMemory_away input be (cell old pool 0) (cell next pool 0) (cell old oldPool offset) (amount kind old.capacity pool) away
  unfold stageMemory
  split
  · exact copied
  · rw [StoreWord.put, if_neg]
    · exact copied
    · intro equal
      have numeric := congrArg BitVec.toNat equal
      have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
      rw [number kind old oldValid oldPool offset inside, number kind next nextValid .header _ fieldInside] at numeric
      have ordered := earlier oldPool .header
      omega

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_frame
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_clock
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_memory
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_preserves_old
