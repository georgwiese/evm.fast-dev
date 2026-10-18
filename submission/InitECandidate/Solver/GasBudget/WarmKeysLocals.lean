import InitECandidate.Solver.GasBudget.WarmKeysProgram
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def inputRegion (start total : Nat) : MemoryRegion.Region := ⟨start, 52 * total + 8⟩
def keyPointer (start index : Nat) : BitVec 64 := BitVec.ofNat 64 (start + 52 * index)

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start total index : Nat) : Prop where
  table : source.locals.lookup (ofString "ak") = some (.val (.word table))
  keys : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 start)))
  count : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 total)))
  index : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))

theorem Locals.of_locals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start total index : Nat}
    (locals : Locals source table start total index) (same : target.locals = source.locals) : Locals target table start total index := by
  constructor <;> rw [same]
  · exact locals.table
  · exact locals.keys
  · exact locals.count
  · exact locals.index

theorem Locals.next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start total index : Nat}
    (locals : Locals source table start total index) :
    Locals (bind source "i" (BitVec.ofNat 64 (index + 1))) table start total (index + 1) :=
  ⟨(bind_lookup_other _ "i" "ak" _ (by decide)).trans locals.table,
    (bind_lookup_other _ "i" "al_keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "i" "nkeys" _ (by decide)).trans locals.count, bind_lookup_same _ _ _⟩

/-- The actual input spacing is 52 bytes; no alignment of an individual
key is assumed. The owned backing interval maps both alternating alignments. -/
theorem query_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start total index : Nat)
    (valid : MemoryRegion.Valid (inputRegion start total)) (inside : index < total)
    (domain : source.memaddrs = InitE.ordinaryDomain) :
    (keyPointer start index).toNat + KeyHash.keySize .storage < 2 ^ 64 ∧
      ∀ offset < KeyHash.keySize .storage, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (keyPointer start index) offset)) := by
  have upper := valid.upper
  change start + (52 * total + 8) ≤ 33806089496 at upper
  have indexBound : start + 52 * index < 2 ^ 64 := by omega
  constructor
  · rw [keyPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
    change start + 52 * index + 52 < 2 ^ 64
    omega
  · intro offset insideKey
    change offset < 52 at insideKey
    rw [domain]
    have mapped := MemoryRegion.byte_mapped (inputRegion start total) valid (52 * index + offset) (by change 52 * index + offset < 52 * total + 8; omega)
    have same : WitnessRadix.byteAddress (keyPointer start index) offset =
        WitnessRadix.byteAddress (MemoryRegion.pointer (inputRegion start total)) (52 * index + offset) := by
      simp only [WitnessRadix.byteAddress, keyPointer, MemoryRegion.pointer, inputRegion, ← BitVec.ofNat_add, Nat.add_assoc]
    rw [same]
    exact mapped

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start total index : Nat)
    (valid : MemoryRegion.Valid (inputRegion start total)) (bounded : index ≤ total) (locals : Locals source table start total index) :
    eval source condition = some (.val (.word (if index < total then 1#64 else 0#64))) := by
  have upper := valid.upper
  change start + (52 * total + 8) ≤ 33806089496 at upper
  have totalSmall : total < 2 ^ 64 := by omega
  have indexSmall : index < 2 ^ 64 := by omega
  have totalSign : total < 2 ^ 63 := by omega
  have indexSign : index < 2 ^ 63 := by omega
  norm_num only [Nat.reducePow] at totalSmall indexSmall totalSign indexSign
  by_cases active : index < total <;>
    simp [eval, condition, localVar, evalHOLFinite, evalHOLExact, toExact, locals.index, locals.count,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt totalSmall, Nat.mod_eq_of_lt indexSmall, totalSign, indexSign, active]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start total index : Nat)
    (locals : Locals source table start total index) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "ak", query, .const 1#64] =
      some (TableCall.values table (keyPointer start index) 1#64) := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, query, locals.table, locals.keys, locals.index,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, TableCall.values, keyPointer, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index 52]

theorem increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start total index : Nat)
    (locals : Locals source table start total index) :
    evaluateHOLFiniteState source increment = (none, bind source "i" (BitVec.ofNat 64 (index + 1))) := by
  apply WitnessRadix.StateSteps.assign_execute source "i" _ _ _ locals.index
  simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, locals.index, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add]

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.Locals.of_locals
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.Locals.next
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.query_geometry
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.condition_read
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.arguments_read
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.increment_execute
