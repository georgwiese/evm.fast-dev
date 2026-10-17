import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.WitnessRadix.ZeroCall
import InitECandidate.Solver.MutableTable.ZeroWords

namespace InitECandidate.Solver.Input.FreshRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {F : Type}

inductive Kind where | transaction | message
  deriving DecidableEq

def size : Kind → Nat | .transaction => 200 | .message => 176
def localName : Kind → String | .transaction => "te" | .message => "m"
def functionName : Kind → String | .transaction => "te_new" | .message => "msg_new"
def clear (kind : Kind) : ProgHOL 64 := .call (some (none, none)) (ofString "memzero")
  [localVar (localName kind), .const (BitVec.ofNat 64 (size kind))]
def finish (kind : Kind) : ProgHOL 64 := .seq (clear kind) (.return (localVar (localName kind)))
def program (kind : Kind) : ProgHOL 64 := .decCall (ofString (localName kind)) .one (ofString "alloc")
  [.const (BitVec.ofNat 64 (size kind))] (finish kind)
def body : Kind → ProgHOL 64
  | .transaction => match Guest.guestFn_te_new with | .function fn => progToHOL fn.body | _ => .skip
  | .message => match Guest.guestFn_msg_new with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape (kind : Kind) : body kind = program kind := by
  cases kind <;> simp only [body, program, finish, clear, size, localName,
    Guest.guestFn_te_new, Guest.guestFn_msg_new, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]

theorem clear_price (kind : Kind) : WitnessRadix.Zero.price (size kind) = 7 := by cases kind <;> decide

def allocated (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.PersistentAlloc.post {source with clock := source.clock - 1}
    pointer (BitVec.ofNat 64 (size kind))) (localName kind) pointer
noncomputable def zeroed (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) :=
  {allocated source kind pointer with
    memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
    clock := source.clock - 9}
noncomputable def closed (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) :=
  restore source (localName kind) (emptyLocalsHOLFinite (zeroed source kind pointer))

/-- Original persistent TE/message constructors, deriving the allocator and
clear executions. Both actual sizes happen to take9body source clocks. -/
theorem execute (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + size kind ≤ 33806089496)
    (mapped : ∀ offset, offset + 8 ≤ size kind → offset % 8 = 0 → source.memaddrs (WitnessRadix.byteAddress pointer offset))
    (enough : 9 ≤ source.clock) :
    evaluateHOLFiniteState source (body kind) = (some (.returned (.val (.word pointer))), closed source kind pointer) := by
  let entered := allocated source kind pointer
  let ready := zeroed source kind pointer
  have pointerLocal : entered.locals.lookup (ofString (localName kind)) = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [localVar (localName kind), .const (BitVec.ofNat 64 (size kind))] = some (WitnessRadix.Zero.values pointer (size kind)) := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, pointerLocal, WitnessRadix.Zero.values]
  have clearRun := WitnessRadix.Zero.call_execute entered _ pointer (size kind) args zeroCode
    (by cases kind <;> decide) (by cases kind <;> decide) aligned mapped
    (by change WitnessRadix.Zero.price (size kind) + 1 ≤ source.clock - 1; rw [clear_price]; omega)
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price (size kind) + 1) = source.clock - 9 := by rw [clear_price]; omega
  change evaluateHOLFiniteState entered (clear kind) = (none, {entered with
    memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
    clock := source.clock - 1 - (WitnessRadix.Zero.price (size kind) + 1)}) at clearRun
  rw [clocks] at clearRun
  change evaluateHOLFiniteState entered (clear kind) = (none, ready) at clearRun
  have readyPointer : ready.locals.lookup (ofString (localName kind)) = some (.val (.word pointer)) := pointerLocal
  have returnRun : evaluateHOLFiniteState ready (.return (localVar (localName kind))) =
      (some (.returned (.val (.word pointer))), emptyLocalsHOLFinite ready) := by
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, readyPointer, shapeOfHOLExact]
  have suffix := WitnessRadix.StateSteps.next_sequence entered ready (clear kind) (.return (localVar (localName kind))) clearRun
    (by change source.clock - 9 ≤ source.clock - 1; omega)
  rw [returnRun] at suffix
  have amountNumber : (BitVec.ofNat 64 (size kind)).toNat = size kind := by cases kind <;> decide
  have allocationRun := WitnessRadix.PersistentAlloc.call_execute source (localName kind)
    [.const (BitVec.ofNat 64 (size kind))] (finish kind) pointer (BitVec.ofNat 64 (size kind)) rfl code heap
    (by rw [amountNumber]; exact room) (by omega)
  change evaluateHOLFiniteState source (program kind) =
    (let output := evaluateHOLFiniteState entered (finish kind)
     (output.1, restore source (localName kind) output.2)) at allocationRun
  change evaluateHOLFiniteState entered (finish kind) = _ at suffix
  rw [suffix] at allocationRun
  rw [body_shape]
  exact allocationRun

theorem canonical (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) :
    emptyLocalsHOLFinite (closed source kind pointer) = emptyLocalsHOLFinite
      {WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind)) with
        memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
        clock := source.clock - 9} := rfl

theorem zero_cell (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64)
    (slot : Nat) (inside : 8 * (slot + 1) ≤ size kind) :
    (closed source kind pointer).memory (pointer + BitVec.ofNat 64 (8 * slot)) = .word 0#64 :=
  MutableTable.ZeroWords.final_cell source.memory pointer (size kind) slot inside

theorem memory_away (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer query : BitVec 64)
    (away : ∀ offset < size kind, query ≠ WitnessRadix.byteAddress pointer offset) :
    (closed source kind pointer).memory query = source.memory query :=
  WitnessRadix.Zero.final_memory_away source.memory pointer query (size kind) away

end InitECandidate.Solver.Input.FreshRecord

#print axioms InitECandidate.Solver.Input.FreshRecord.body_shape
#print axioms InitECandidate.Solver.Input.FreshRecord.clear_price
#print axioms InitECandidate.Solver.Input.FreshRecord.execute
#print axioms InitECandidate.Solver.Input.FreshRecord.canonical
#print axioms InitECandidate.Solver.Input.FreshRecord.zero_cell
#print axioms InitECandidate.Solver.Input.FreshRecord.memory_away
