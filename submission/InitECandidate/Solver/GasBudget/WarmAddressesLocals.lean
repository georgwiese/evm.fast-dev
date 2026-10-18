import InitECandidate.Solver.GasBudget.WarmAddressesProgram
import InitECandidate.Solver.MutableTable.PointerArray

namespace InitECandidate.Solver.GasBudget.WarmAddresses
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start count index : Nat) : Prop where
  table : source.locals.lookup (ofString "aa") = some (.val (.word table))
  addresses : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 start)))
  count : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (count - 1))))
  index : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))

theorem Locals.of_locals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start count index : Nat}
    (locals : Locals source table start count index) (same : target.locals = source.locals) : Locals target table start count index := by
  constructor <;> rw [same]
  · exact locals.table
  · exact locals.addresses
  · exact locals.count
  · exact locals.index

theorem Locals.next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start count index : Nat}
    (locals : Locals source table start count index) : Locals (bind source "i" (BitVec.ofNat 64 (index + 1))) table start count (index + 1) :=
  ⟨(bind_lookup_other _ "i" "aa" _ (by decide)).trans locals.table,
    (bind_lookup_other _ "i" "al_addrs" _ (by decide)).trans locals.addresses,
    (bind_lookup_other _ "i" "nal" _ (by decide)).trans locals.count, bind_lookup_same _ _ _⟩

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start count index : Nat)
    (valid : MemoryRegion.Valid ⟨start, 8 * count⟩) (positive : 0 < count) (bounded : index ≤ count) (locals : Locals source table start count index) :
    eval source condition = some (.val (.word (if index < count then 1#64 else 0#64))) := by
  have upper := valid.upper
  change start + 8 * count ≤ 33806089496 at upper
  have countSmall : count < 2 ^ 64 := by omega
  have indexSmall : index < 2 ^ 64 := by omega
  have countSign : count < 2 ^ 63 := by omega
  have indexSign : index < 2 ^ 63 := by omega
  have successor : BitVec.ofNat 64 (count - 1) + 1#64 = BitVec.ofNat 64 count := by
    change BitVec.ofNat 64 (count - 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 count
    rw [← BitVec.ofNat_add, show count - 1 + 1 = count from by omega]
  norm_num only [Nat.reducePow] at countSmall indexSmall countSign indexSign
  by_cases active : index < count <;>
    simp [eval, condition, total, localVar, evalHOLExact, evalListHOLExact, toExact, locals.index, locals.count,
      valueIsWord, valueWord, wordOpHOL, wordOp, successor,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt indexSmall, countSign, indexSign, active]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start count index floor : Nat) (pointers : Nat → BitVec 64)
    (array : PointerArray source.memory 20 start count floor pointers) (inside : index < count) (domain : source.memaddrs = InitE.ordinaryDomain)
    (locals : Locals source table start count index) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "aa", query, .const 1#64] =
      some (TableCall.values table (pointers index) 1#64) := by
  have scaled : BitVec.ofNat 64 start + BitVec.ofNat 64 index * 8#64 = pointerCell start index := by
    change BitVec.ofNat 64 start + BitVec.ofNat 64 index * BitVec.ofNat 64 8 = pointerCell start index
    simp only [pointerCell, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index 8]
  have mapped : source.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 index * 8#64) := by rw [scaled, domain]; exact array.cell_mapped index inside
  have stored : source.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 index * 8#64) = .word (pointers index) := by rw [scaled]; exact array.words index inside
  have read : eval source query = some (.val (.word (pointers index))) := by
    simp [eval, query, localVar, evalHOLExact, evalListHOLExact, toExact, locals.addresses, locals.index,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL, mapped, stored]
  simp only [eval] at read
  simp [evalListHOLFinite, evalListHOLExact, read, localVar, evalHOLExact, toExact, locals.table, TableCall.values]

theorem increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start count index : Nat)
    (locals : Locals source table start count index) : evaluateHOLFiniteState source increment = (none, bind source "i" (BitVec.ofNat 64 (index + 1))) := by
  apply WitnessRadix.StateSteps.assign_execute source "i" _ _ _ locals.index
  simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, locals.index, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add]

end InitECandidate.Solver.GasBudget.WarmAddresses

#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.Locals.of_locals
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.Locals.next
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.condition_read
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.arguments_read
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.increment_execute
