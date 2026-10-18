import InitECandidate.Solver.GasBudget.WarmKeysLocals
import InitECandidate.Solver.MutableTable.SetModelCursor
import InitECandidate.Solver.MutableTable.SetAmortized

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  domain : source.memaddrs = InitE.ordinaryDomain
  little : source.be = false
  allocCode : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one)
  trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one)
  zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one)
  hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one)
  copyCode : source.code.lookup (ofString "memcpy") = some (WitnessRadix.CopyGeneral.formals, WitnessRadix.Copy32.body, .one)
  memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one)
  findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one)
  insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one)
  growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one)
  setCode : source.code.lookup (ofString "htab_set") = some (TableCall.formals, Set.body, .one)

theorem Environment.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (environment : Environment source)
    (codes : target.code = source.code) (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) : Environment target := by
  rcases environment with ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩
  constructor
  · exact domain.trans a
  · exact endian.trans b
  · rw [codes]; exact c
  · rw [codes]; exact d
  · rw [codes]; exact e
  · rw [codes]; exact f
  · rw [codes]; exact g
  · rw [codes]; exact h
  · rw [codes]; exact i
  · rw [codes]; exact j
  · rw [codes]; exact k
  · rw [codes]; exact l

structure Table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : Plan) (slots : List Nat) (cursor floor : Nat) : Prop where
  valid : Valid .storage plan
  half : 2 * slots.length ≤ plan.capacity
  header : MemoryModel.Header source.memory .storage plan (BitVec.ofNat 64 slots.length)
  occupied : MemoryModel.Occupied source .storage plan slots
  power : ∃ bits, plan.capacity = 2 ^ bits ∧ 2 ≤ bits
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))
  bounded : cursor ≤ 33806089496
  aligned : cursor % 8 = 0
  earlier : ∀ pool, plan.base pool + size .storage plan pool ≤ cursor
  lower : ∀ pool, floor ≤ plan.base pool

theorem Table.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {plan : Plan} {slots : List Nat} {cursor floor : Nat}
    (table : Table source plan slots cursor floor) (globals : target.globals = source.globals) (memory : target.memory = source.memory)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) : Table target plan slots cursor floor := by
  refine ⟨table.valid, table.half, ?_, ?_, table.power, ?_, table.bounded, table.aligned, table.earlier, table.lower⟩
  · rw [memory]; exact table.header
  · exact MemoryModel.Occupied.of_fields source target .storage plan slots table.occupied memory.symm domain.symm endian.symm
  · rw [globals]; exact table.heap

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.Environment.of_fields
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.Table.of_fields
