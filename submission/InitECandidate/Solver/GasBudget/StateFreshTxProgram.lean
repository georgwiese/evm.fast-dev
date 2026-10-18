import InitECandidate.Solver.GasBudget.JournalTableAssign
import InitECandidate.Solver.MutableTable.FamilyRegion
import InitECandidate.Solver.Input.GlobalFieldStore

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

structure Spec where
  kind : KeyHash.Kind
  bits : Nat
  offset : Nat
  deriving DecidableEq

def Spec.capacity (spec : Spec) : Nat := 2 ^ spec.bits
def Spec.Valid (spec : Spec) : Prop := 3 ≤ spec.bits ∧ spec.bits ≤ 32 ∧ 8 ≤ spec.offset ∧ spec.offset + 8 ≤ 72 ∧ spec.offset % 8 = 0
def Spec.arguments (spec : Spec) : List (ExpHOL 64) := [.const (BitVec.ofNat 64 (KeyHash.keySize spec.kind)), .const (BitVec.ofNat 64 spec.capacity)]
def Spec.call (spec : Spec) : ProgHOL 64 := .call (some (some (.local, ofString "t"), none)) (ofString "htab_new") spec.arguments
def Spec.store (spec : Spec) : ProgHOL 64 := .store (addConst (.var .global (ofString "ts")) (BitVec.ofNat 64 spec.offset)) (localVar "t")
def Spec.price (spec : Spec) : Nat := TableRuntime.price spec.capacity + 1
def reset : ProgHOL 64 := .assign .global (ofString "journal_n") (.const 0#64)
def tailProgram : List Spec → ProgHOL 64
  | [] => .seq reset (.return (.const 0#64))
  | spec :: rest => .seq spec.call (.seq spec.store (tailProgram rest))
def first : Spec := ⟨.account, 6, 8⟩
def rest : List Spec := [⟨.account, 6, 16⟩, ⟨.storage, 6, 24⟩, ⟨.account, 4, 32⟩,
  ⟨.storage, 4, 40⟩, ⟨.word, 4, 48⟩, ⟨.account, 4, 56⟩, ⟨.storage, 4, 64⟩]
def allocate : ProgHOL 64 := .call (some (some (.global, ofString "ts"), none)) (ofString "alloc") [.const 72#64]
def storeBlockState : ProgHOL 64 := .store (addConst (.var .global (ofString "ts")) 0#64) (.var .global (ofString "bs"))
def afterBlockState : ProgHOL 64 := .decCall (ofString "t") .one (ofString "htab_new") first.arguments (.seq first.store (tailProgram rest))
def afterAllocation : ProgHOL 64 := .seq storeBlockState afterBlockState
def program : ProgHOL 64 := .seq allocate afterAllocation
def body : ProgHOL 64 := match Guest.guestFn_state_fresh_tx with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = program := by
  simp only [body, Guest.guestFn_state_fresh_tx, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_some,
    program, allocate, afterAllocation, storeBlockState, afterBlockState, first, rest, tailProgram, reset,
    Spec.arguments, Spec.call, Spec.store, Spec.capacity, KeyHash.keySize, localVar, addConst]
  rfl

theorem specs_valid : ∀ spec ∈ first :: rest, spec.Valid := by
  intro spec member
  simp only [first, rest, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Spec.Valid <;> decide

theorem offsets_distinct : ((first :: rest).map Spec.offset).Nodup := by decide

def price (specs : List Spec) : Nat := (specs.map Spec.price).sum
theorem price_all : 1 + price (first :: rest) = 81 := by decide
def cursor (start : Nat) : List Spec → Nat
  | [] => start
  | spec :: rest => cursor (freshEnd spec.kind start spec.capacity) rest

theorem cursor_all (start : Nat) : cursor (start + 72) (first :: rest) = start + 17176 := by
  simp only [cursor, first, rest, Spec.capacity, freshEnd, stride, rounded, KeyHash.keySize]
  omega

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.body_shape
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.specs_valid
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.offsets_distinct
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.price_all
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.cursor_all
