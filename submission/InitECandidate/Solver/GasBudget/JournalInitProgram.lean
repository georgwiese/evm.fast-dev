import InitECandidate.Solver.GasBudget.JournalZone
import InitECandidate.Solver.Input.GlobalAssignNormal
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal

namespace InitECandidate.Solver.GasBudget.Journal.Initialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def capacity : Nat := 524288
def bytes : Nat := capacity * 32
def setCap : ProgHOL 64 := .assign .global (ofString "journal_cap") (.const (BitVec.ofNat 64 capacity))
def allocationArguments : List (ExpHOL 64) := [.panop .mul [.var .global (ofString "journal_cap"), .const 32#64]]
def allocate : ProgHOL 64 := .call (some (some (.global, ofString "journal"), none)) (ofString "alloc") allocationArguments
def resetCounter : ProgHOL 64 := .assign .global (ofString "journal_n") (.const 0#64)
def resetTransaction : ProgHOL 64 := .assign .global (ofString "ts") (.const 0#64)
def afterAllocation : ProgHOL 64 := .seq resetCounter (.seq resetTransaction (.return (.const 0#64)))
def program : ProgHOL 64 := .seq setCap (.seq allocate afterAllocation)

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.seq (.assign .global name _) rest) => (if name = ofString "journal_cap" then [code] else []) ++ sites rest
  | .seq first second | .ite _ first second => sites first ++ sites second
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest => sites rest
  | _ => []
def selected : ProgHOL 64 := match Guest.guestFn_state_init with
  | .function fn => ((sites (progToHOL fn.body))[0]?).getD .skip
  | _ => .skip

set_option maxRecDepth 10000 in
theorem actual_site : selected = program := by
  simp only [selected, Guest.guestFn_state_init, progToHOL, expToHOL, shapeToHOL, sites, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    program, setCap, allocate, allocationArguments, afterAllocation, resetCounter, resetTransaction, capacity]

def capState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := Input.putGlobal source "journal_cap" (BitVec.ofNat 64 capacity)
def allocatedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  Input.putGlobal {capState source with globals := (capState source).globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (cursor + bytes)))), clock := source.clock - 1}
    "journal" (BitVec.ofNat 64 cursor)
def counterState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := Input.putGlobal (allocatedState source cursor) "journal_n" 0#64
def initialized (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := Input.putGlobal (counterState source cursor) "ts" 0#64

end InitECandidate.Solver.GasBudget.Journal.Initialization

#print axioms InitECandidate.Solver.GasBudget.Journal.Initialization.actual_site
