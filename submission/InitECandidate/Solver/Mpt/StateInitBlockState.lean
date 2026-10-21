import InitECandidate.Solver.Mpt.StateInitBlockProgram
import InitECandidate.Solver.MutableTable.TableRuntime.AssignedNormal
import InitECandidate.Solver.Input.GlobalFieldStore

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def writeField (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block offset : Nat) (value : BitVec 64):=
  {source with memory:=StoreWord.put source.memory (MemoryRegion.address ⟨block,80⟩ offset) value}
def stepState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) : Action → PanSemStateFiniteExact 64 Guest.HostMemory
  | .table kind bits offset=>writeField (TableRuntime.callState source "t" kind start (2^bits)) block offset (BitVec.ofNat 64 start)
  | .scalar offset value=>writeField source block offset value
def stepCursor (start : Nat) : Action → Nat
  | .table kind bits _=>NaturalLayout.freshEnd kind start (2^bits)
  | .scalar ..=>start
def stepPrice : Action → Nat
  | .table _ bits _=>TableRuntime.price (2^bits)+1
  | .scalar ..=>0
def StepLayout (start : Nat) : Action → Prop
  | .table kind bits _=>NaturalLayout.Valid kind (NaturalLayout.fresh kind start (2^bits))
  | .scalar ..=>True
def walk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) : List Action → PanSemStateFiniteExact 64 Guest.HostMemory
  | []=>source
  | action::rest=>walk (stepState source block start action) block (stepCursor start action) rest
def Layouts (start : Nat) : List Action → Prop
  | []=>True
  | action::rest=>StepLayout start action ∧ Layouts (stepCursor start action) rest

theorem step_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action) :
    (stepState source block start action).clock=source.clock-stepPrice action:=by cases action <;> rfl

theorem step_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start)))) :
    (stepState source block start action).globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (stepCursor start action)))):=by
  cases action <;> simp [stepState,writeField,stepCursor,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,heap]

theorem step_bs (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action)
    (bs : source.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩)))) :
    (stepState source block start action).globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩))):=by
  cases action <;> simpa [stepState,writeField,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "heap_ptr"≠ofString "bs" from by decide] using bs

theorem step_t (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action) (old : BitVec 64)
    (cell : source.locals.lookup (ofString "t")=some (.val (.word old))) :
    ∃ value,(stepState source block start action).locals.lookup (ofString "t")=some (.val (.word value)):=by
  cases action with
  | table kind bits offset=>exact ⟨BitVec.ofNat 64 start,bind_lookup_same _ _ _⟩
  | scalar offset value=>exact ⟨old,cell⟩

theorem walk_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (actions : List Action) :
    (walk source block start actions).clock=source.clock-price actions:=by
  induction actions generalizing source start with
  | nil=>rfl
  | cons action rest ih=>
    rw [walk,ih,step_clock,Nat.sub_sub]
    cases action <;> simp [stepPrice,price]

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_clock
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_heap
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_bs
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_t
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_clock
