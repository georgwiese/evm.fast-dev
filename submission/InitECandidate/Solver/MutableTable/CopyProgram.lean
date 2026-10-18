import InitECandidate.Solver.MutableTable.KeysProgram
import InitECandidate.Solver.MutableTable.NaturalLayoutFresh
import InitECandidate.Solver.WitnessRadix.ProgramPrefixAppend

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def body : ProgHOL 64 := match Guest.guestFn_htab_copy with | .function fn => progToHOL fn.body | _ => .skip
def name : Pool → String
  | .header => "n" | .keys => "keys" | .values => "vals"
  | .used => "used" | .order => "order" | .position => "order_pos"
def headerOffset : Pool → Nat
  | .header => 0 | .keys => 32 | .values => 40 | .used => 48 | .order => 56 | .position => 64
def amount (kind : KeyHash.Kind) (capacity : Nat) : Pool → Nat
  | .header => 72 | .keys => stride kind * capacity | .used => capacity | _ => 8 * capacity
def amountExpression : Pool → ExpHOL 64
  | .header => .const 72#64
  | .keys => .panop .mul [localVar "cap", localVar "stride"]
  | .used => localVar "cap"
  | _ => .panop .mul [localVar "cap", .const 8#64]
def sourceExpression : Pool → ExpHOL 64
  | .header => localVar "t"
  | pool => Find.tableLoad (BitVec.ofNat 64 (headerOffset pool))
def copyCall (pool : Pool) : ProgHOL 64 :=
  .call (some (none, none)) (ofString "memcpy") [localVar (name pool), sourceExpression pool, amountExpression pool]
def pointerStore (pool : Pool) : ProgHOL 64 :=
  .store (.op .add [localVar "n", .const (BitVec.ofNat 64 (headerOffset pool))]) (localVar (name pool))
def stageActions (pool : Pool) : List Action :=
  [.allocate (name pool) (amountExpression pool), .command (copyCall pool)] ++
    if pool = .header then [] else [.command (pointerStore pool)]
def pools : List Pool := [.header, .keys, .values, .used, .order, .position]
def actions : List Action := [.declare "cap" (Find.tableLoad 16#64), .declare "stride" (Find.tableLoad 8#64)] ++ pools.flatMap stageActions

/-- Exact shape of the original persistent copy implementation. -/
theorem body_shape : body = program actions (.return (localVar "n")) := by
  simp only [body, Guest.guestFn_htab_copy, progToHOL, expToHOL, shapeToHOL,
    actions, pools, stageActions, copyCall, pointerStore, sourceExpression, amountExpression, name, headerOffset,
    program, Find.tableLoad, localVar, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, Option.map_none, ↓reduceIte]
  rfl

def region (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) : MemoryRegion.Region :=
  ⟨plan.base pool, size kind plan pool⟩

theorem amount_room (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) : amount kind plan.capacity pool ≤ size kind plan pool := by
  cases pool <;> simp only [amount, size, le_refl]
  exact (rounded_bounds plan.capacity).1

theorem amount_round (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) : rounded (amount kind plan.capacity pool) = size kind plan pool := by
  have multiple := (stride_bounds kind).2.2
  have productMultiple : stride kind * plan.capacity % 8 = 0 := by simp only [Nat.mul_mod, multiple, Nat.zero_mul, Nat.zero_mod]
  cases pool <;> simp only [amount, size, rounded]
  all_goals omega

theorem amount_multiple (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) (notUsed : pool ≠ .used) : amount kind plan.capacity pool % 8 = 0 := by
  have multiple := (stride_bounds kind).2.2
  cases pool <;> simp_all [amount, Nat.mul_mod]

theorem region_pointer (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) :
    MemoryRegion.pointer (region kind plan pool) = cell plan pool 0 := by
  simp only [MemoryRegion.pointer, region, cell, Nat.add_zero]

theorem region_address (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) (offset : Nat) :
    byteAddress (MemoryRegion.pointer (region kind plan pool)) offset = cell plan pool offset := by
  rw [region_pointer, offset_cell]

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.body_shape
#print axioms InitECandidate.Solver.MutableTable.TableCopy.amount_room
#print axioms InitECandidate.Solver.MutableTable.TableCopy.amount_round
#print axioms InitECandidate.Solver.MutableTable.TableCopy.amount_multiple
#print axioms InitECandidate.Solver.MutableTable.TableCopy.region_pointer
#print axioms InitECandidate.Solver.MutableTable.TableCopy.region_address
