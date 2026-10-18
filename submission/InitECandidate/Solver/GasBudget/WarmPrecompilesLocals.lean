import InitECandidate.Solver.GasBudget.WarmPrecompilesProgram
import InitECandidate.Solver.MutableTable.MemoryRegionQuery

namespace InitECandidate.Solver.GasBudget.WarmPrecompiles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def keyPointer (start index : Nat) : BitVec 64 := BitVec.ofNat 64 (start + 20 * index)
structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start index : Nat) : Prop where
  table : source.locals.lookup (ofString "aa") = some (.val (.word table))
  keys : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 start)))
  index : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))

theorem Locals.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start index : Nat}
    (locals : Locals source table start index) (same : target.locals = source.locals) (globals : target.globals = source.globals) : Locals target table start index :=
  ⟨by rw [same]; exact locals.table, by rw [globals]; exact locals.keys, by rw [same]; exact locals.index⟩

theorem Locals.next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table : BitVec 64} {start index : Nat}
    (locals : Locals source table start index) : Locals (bind source "i" (BitVec.ofNat 64 (index + 1))) table start (index + 1) :=
  ⟨(bind_lookup_other _ "i" "aa" _ (by decide)).trans locals.table, locals.keys, bind_lookup_same _ _ _⟩

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start index : Nat)
    (bounded : index ≤ 18) (locals : Locals source table start index) :
    eval source condition = some (.val (.word (if index < 18 then 1#64 else 0#64))) := by
  have indexSmall : index < 18446744073709551616 := by omega
  have indexSign : index < 9223372036854775808 := by omega
  by_cases active : index < 18 <;>
    simp [eval, condition, localVar, evalHOLExact, toExact, locals.index,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexSmall, indexSign, active]

theorem query_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start index : Nat)
    (valid : MemoryRegion.Valid ⟨start, 360⟩) (inside : index < 18) (domain : source.memaddrs = InitE.ordinaryDomain) :
    (keyPointer start index).toNat + KeyHash.keySize .account < 2 ^ 64 ∧
      ∀ offset < KeyHash.keySize .account, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (keyPointer start index) offset)) :=
  MemoryRegion.strided_query source ⟨start, 360⟩ valid 20 index 20 (by change 20 * index + 20 ≤ 360; omega) domain

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start index : Nat)
    (locals : Locals source table start index) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "aa", query, .const 1#64] =
      some (TableCall.values table (keyPointer start index) 1#64) := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, query, locals.table, locals.keys, locals.index,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, TableCall.values, keyPointer, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index 20]

theorem increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (start index : Nat)
    (locals : Locals source table start index) : evaluateHOLFiniteState source increment = (none, bind source "i" (BitVec.ofNat 64 (index + 1))) := by
  apply WitnessRadix.StateSteps.assign_execute source "i" _ _ _ locals.index
  simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, locals.index, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add]

end InitECandidate.Solver.GasBudget.WarmPrecompiles

#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.Locals.of_fields
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.Locals.next
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.condition_read
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.query_geometry
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.arguments_read
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.increment_execute
