import InitECandidate.Solver.Input.OriginalScalarGlobals
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Input.InitializerAllocations
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Action where
  name : String
  bytes : Nat
  expression : ExpHOL 64

def constant (name : String) (bytes : Nat) : Action := ⟨name,bytes,.const (BitVec.ofNat 64 bytes)⟩
def call (action : Action) : ProgHOL 64 :=
  .call (some (some (.global,ofString action.name),none)) (ofString "alloc") [action.expression]
def program : List Action → ProgHOL 64
  | [] => .return (.const 0#64)
  | action :: rest => .seq (call action) (program rest)
def withTail : List Action → ProgHOL 64 → ProgHOL 64
  | [],tail => tail
  | action :: rest,tail => .seq (call action) (withTail rest tail)

theorem program_tail (actions : List Action) : program actions = withTail actions (.return (.const 0#64)) := by
  induction actions with
  | nil => rfl
  | cons action rest ih => simp only [program,withTail,ih]

def totalBytes : List Action → Nat
  | [] => 0
  | action :: rest => action.bytes + totalBytes rest
def reserve (source : PanSemStateFiniteExact 64 Guest.HostMemory) (action : Action) (cursor : Nat) :=
  putGlobal {source with globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (cursor + action.bytes))))} action.name (BitVec.ofNat 64 cursor)
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : List Action → PanSemStateFiniteExact 64 Guest.HostMemory
  | [] => source
  | action :: rest => template (reserve source action cursor) (cursor + action.bytes) rest

structure Valid (action : Action) : Prop where
  member : ofString action.name ∈ OriginalScalarGlobals.names
  different : ofString action.name ≠ ofString "heap_ptr"
  aligned : action.bytes % 8 = 0
  read : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,WitnessRadix.QueryBranch.eval source action.expression = some (.val (.word (BitVec.ofNat 64 action.bytes)))

theorem valid_constant (name : String) (bytes : Nat) (member : ofString name ∈ OriginalScalarGlobals.names)
    (different : ofString name ≠ ofString "heap_ptr") (aligned : bytes % 8 = 0) : Valid (constant name bytes) :=
  ⟨member,different,aligned,fun _ => rfl⟩

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) (clock : Nat) :
    template {source with clock := clock} cursor actions = {template source cursor actions with clock := clock} := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor actions).globals := by
  induction actions generalizing source cursor with
  | nil => exact scalars
  | cons action rest ih =>
    exact ih (reserve source action cursor) (cursor + action.bytes)
      ((scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (cursor + action.bytes))).update (ofString action.name) (BitVec.ofNat 64 cursor))

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : ∀ action,action ∈ actions → Valid action) :
    (template source cursor actions).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + totalBytes actions)))) := by
  induction actions generalizing source cursor with
  | nil => simpa only [template,totalBytes,Nat.add_zero] using heap
  | cons action rest ih =>
    have current := valid action (by simp)
    have nextHeap : (reserve source action cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + action.bytes)))) := by
      simp [reserve,putGlobal,HolFiniteMapExact.update,FUPDATE,current.different]
    have next := ih (reserve source action cursor) (cursor + action.bytes) nextHeap (fun item member => valid item (List.mem_cons_of_mem _ member))
    simpa only [template,totalBytes,Nat.add_assoc] using next

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (different : ∀ action,action ∈ actions → key ≠ ofString action.name) :
    (template source cursor actions).globals.lookup key = source.globals.lookup key := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih =>
    have next := ih (reserve source action cursor) (cursor + action.bytes) (fun item member => different item (List.mem_cons_of_mem _ member))
    have other := different action (by simp)
    simpa only [template] using next.trans (by simp [reserve,putGlobal,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm other])

/-- Execute a literal initializer allocation segment, charging each genuine
allocator caller once. Current typed globals and aggregate room suffice. -/
theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : ∀ action,action ∈ actions → Valid action) (room : cursor + totalBytes actions ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : actions.length ≤ source.clock) :
    evaluateHOLFiniteState source (withTail actions continuation) =
      evaluateHOLFiniteState {template source cursor actions with clock := source.clock - actions.length} continuation := by
  induction actions generalizing source cursor with
  | nil => simp only [withTail,template,List.length_nil,Nat.sub_zero]
  | cons action rest ih =>
    have current := valid action (by simp)
    have tailValid : ∀ item,item ∈ rest → Valid item := fun item member => valid item (List.mem_cons_of_mem _ member)
    have totalRoom : cursor + action.bytes + totalBytes rest ≤ 33806089496 := by simpa only [totalBytes,Nat.add_assoc] using room
    obtain ⟨old,present⟩ := scalars (ofString action.name) current.member
    have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [action.expression] = some (PersistentAlloc.values (BitVec.ofNat 64 action.bytes)) := by
      have read := current.read source
      simp only [WitnessRadix.QueryBranch.eval] at read
      simp [evalListHOLFinite,evalListHOLExact,read,PersistentAlloc.values]
    let next := {reserve source action cursor with clock := source.clock - 1}
    have firstRun := PersistentAlloc.global_call_execute_expected source action.name old cursor action.bytes (cursor + action.bytes) (by omega) (Nat.le_refl _) (by omega)
      (by have := current.aligned; omega) present [action.expression] args (PersistentAlloc.original_code source.code installed) heap (by simp only [List.length_cons] at enough; omega)
    have nextScalars : OriginalScalarGlobals.Scalars next.globals :=
      (scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (cursor + action.bytes))).update (ofString action.name) (BitVec.ofNat 64 cursor)
    have nextHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + action.bytes)))) := by
      simp [next,reserve,putGlobal,HolFiniteMapExact.update,FUPDATE,current.different]
    have back := ih next (cursor + action.bytes) installed nextScalars nextHeap tailValid totalRoom (by have := current.aligned; omega)
      (by change rest.length ≤ source.clock - 1; simp only [List.length_cons] at enough; omega)
    rw [withTail]
    simp only [call]
    rw [StateSteps.next_sequence source next _ _ firstRun (by change source.clock - 1 ≤ source.clock; omega)]
    have subtract : source.clock - 1 - rest.length = source.clock - (action :: rest).length := by simp only [List.length_cons]; omega
    simpa only [next,template_clock,subtract,template] using back

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : ∀ action,action ∈ actions → Valid action) (room : cursor + totalBytes actions ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : actions.length ≤ source.clock) :
    evaluateHOLFiniteState source (program actions) =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor actions with clock := source.clock - actions.length}) := by
  rw [program_tail,execute_prefix source cursor actions (.return (.const 0#64)) installed scalars heap valid room aligned enough]
  simpa only [BuildEntry.returnZero] using BuildEntry.zero_return {template source cursor actions with clock := source.clock - actions.length}

end InitECandidate.Solver.Input.InitializerAllocations

#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_clock
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_scalars
#print axioms InitECandidate.Solver.Input.InitializerAllocations.execute
#print axioms InitECandidate.Solver.Input.InitializerAllocations.valid_constant
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_heap
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_other

#print axioms InitECandidate.Solver.Input.InitializerAllocations.withTail
#print axioms InitECandidate.Solver.Input.InitializerAllocations.program_tail
#print axioms InitECandidate.Solver.Input.InitializerAllocations.execute_prefix
