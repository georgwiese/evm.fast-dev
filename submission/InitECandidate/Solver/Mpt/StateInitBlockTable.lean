import InitECandidate.Solver.Mpt.StateInitBlockRuntime
import InitECandidate.Solver.MutableTable.TableRuntime.ModelCaller
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString

theorem step_grows (start : Nat) (action : Action) : start≤stepCursor start action:=by
  cases action <;> dsimp only [stepCursor,freshEnd] <;> omega

theorem cursor_grows (start : Nat) (specs : List Action) : start≤cursor start specs:=by
  induction specs generalizing start with
  | nil=>exact Nat.le_refl _
  | cons action rest ih=>
    rw [cursor_cons]
    exact (step_grows start action).trans (ih (stepCursor start action))

/-- The physical end of every real initialized prefix is read from its
last actual layout, rather than assumed for future allocations. -/
theorem layouts_end (start : Nat) (specs : List Action) (layouts : Layouts start specs)
    (bounded : start≤33806089496) (aligned : start%8=0) :
    cursor start specs≤33806089496 ∧ cursor start specs%8=0:=by
  induction specs generalizing start with
  | nil=>exact ⟨bounded,aligned⟩
  | cons action rest ih=>
    rw [cursor_cons]
    apply ih (stepCursor start action) layouts.2
    · cases action with
      | scalar offset value=>exact bounded
      | table kind bits offset=>exact layouts.1.upper .position
    · cases action with
      | scalar offset value=>exact aligned
      | table kind bits offset=>
        have position:=layouts.1.aligned .position
        change ((fresh kind start (2^bits)).base .position+8*(2^bits))%8=0
        rw [Nat.add_mod,position]
        omega

/-- A current table survives actual later block constructors and field
writes when its complete pools lie after the block and before that prefix. -/
theorem table_after_walk (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (floor : Nat)
    (table : TableState source kind plan slots start floor)
    (recordValid : MemoryRegion.Valid ⟨block,80⟩) (wellFormed : ∀ action∈specs,action.Valid)
    (layouts : Layouts start specs) (afterBlock : ∀ pool,block+80≤plan.base pool) :
    TableState (walk source block start specs) kind plan slots (cursor start specs) floor:=by
  have bounds:=layouts_end start specs layouts table.bounded table.aligned
  have pools : MemoryModel.PoolFrame source.memory (walk source block start specs).memory kind plan:=by
    intro pool offset inside
    apply walk_old_word specs source block start recordValid wellFormed layouts
    · rw [number kind plan table.valid pool offset inside]
      have before:=table.earlier pool
      omega
    · right
      rw [number kind plan table.valid pool offset inside]
      exact (afterBlock pool).trans (Nat.le_add_right _ _)
  exact ⟨table.valid,table.half,table.header.of_pool_frame _ _ _ _ _ pools,
    table.occupied.of_pool_frame source _ kind plan table.valid slots (walk_domain specs source block start)
      (walk_endian specs source block start) pools,table.power,walk_heap specs source block start table.heap,
    bounds.1,bounds.2,(fun pool=>(table.earlier pool).trans (cursor_grows start specs)),table.lower⟩

/-- Each real constructor followed by its lower block pointer store creates
the empty physical table at its actual next heap. -/
theorem table_at_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start bits offset : Nat)
    (kind : KeyHash.Kind) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (validAction : (Action.table kind bits offset).Valid) (before : block+80≤start)
    (valid : Valid kind (fresh kind start (2^bits)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false) :
    TableState (stepState source block start (.table kind bits offset)) kind (fresh kind start (2^bits)) []
      (freshEnd kind start (2^bits)) start:=by
  let called:=TableRuntime.callState source "t" kind start (2^bits)
  let target:=stepState source block start (.table kind bits offset)
  have pools : MemoryModel.PoolFrame called.memory target.memory kind (fresh kind start (2^bits)):=by
    intro pool i inside
    change StoreWord.put called.memory (MemoryRegion.address ⟨block,80⟩ offset) (BitVec.ofNat 64 start) (cell _ pool i)=_
    apply if_neg
    intro same
    have numbers:=congrArg BitVec.toNat same
    rw [number kind _ valid pool i inside,MemoryRegion.address_number ⟨block,80⟩ recordValid offset (by have h:=validAction.2.2.1; change offset≤80; omega)] at numbers
    have lower:=(fresh_bounds kind start (2^bits) pool).1
    change (fresh kind start (2^bits)).base pool+i=block+offset at numbers
    have h:=validAction.2.2.1
    omega
  have header:=TableRuntime.caller_header source "t" kind start (2^bits) valid
  have occupied:=TableRuntime.caller_model source "t" kind start (2^bits) valid
    (Or.inr (capacity_bounds kind bits validAction.1 validAction.2.1).2.1) domain little
  have bound : freshEnd kind start (2^bits)≤33806089496:=valid.upper .position
  have alignment : freshEnd kind start (2^bits)%8=0:=by
    have position:=valid.aligned .position
    change ((fresh kind start (2^bits)).base .position+8*(2^bits))%8=0
    rw [Nat.add_mod,position]
    omega
  refine ⟨valid,by simp,header.of_pool_frame _ _ _ _ _ pools,
    occupied.of_pool_frame called target kind _ valid [] rfl rfl pools,⟨bits,rfl,by have h:=validAction.1; omega⟩,
    ?_,bound,alignment,(fun pool=>(fresh_bounds kind start (2^bits) pool).2),(fun pool=>(fresh_bounds kind start (2^bits) pool).1)⟩
  simp [stepState,writeField,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_grows
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.cursor_grows
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.layouts_end
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.table_after_walk
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.table_at_step
