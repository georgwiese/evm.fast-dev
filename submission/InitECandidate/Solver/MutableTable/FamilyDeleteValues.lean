import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.MutableTable.DeleteNormalCallValues
import InitECandidate.Solver.MutableTable.FamilyValues

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix NaturalLayout

/-- Actual deletion retains every live table and its stable pointer. The
deleted table changes only its population/occupied representation; no heap
allocation or entry-clock allowance is assumed. -/
theorem delete_normal_values {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → Object) (writer : ι) (family : Model source cursor objects)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : ValuesHave source objects property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ (paid : Nat) (next : Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧ next.floor = (objects writer).floor ∧
      Model target cursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length - 1 ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length ∧
      target.locals = source.locals ∧ target.globals = source.globals ∧ target.code = source.code ∧
      GasBudget.WarmKeys.Environment target ∧
      (∀ address, TableFootprint.Outside (objects writer).kind (objects writer).plan address → target.memory address = source.memory address) ∧ ValuesHave target (Function.update objects writer next) property := by
  let old := objects writer
  have table := family.tables writer
  obtain ⟨paid, memory, slots, flag, bounded, fits, frame, post, half, writerValues⟩ :=
    Delete.model_call_normal_values source target old.kind old.plan old.slots cursor old.floor table environment query queryFits queryMapped deleteCode arguments args (property writer) (values writer) normal
  let next : Object := {old with slots := slots}
  have memoryEq : target.memory = memory := congrArg PanSemStateFiniteExact.memory frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change target.globals = source.globals at globals
  have codes := congrArg PanSemStateFiniteExact.code frame
  change target.code = source.code at codes
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  change target.memaddrs = source.memaddrs at domain
  have endian := congrArg PanSemStateFiniteExact.be frame
  change target.be = source.be at endian
  have locals := congrArg PanSemStateFiniteExact.locals frame
  change target.locals = source.locals at locals
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change target.clock = source.clock - paid at clock
  have heap := congrArg (fun g => g.lookup (ofString "heap_ptr")) globals
  have writerTable : TableState target next.kind next.plan next.slots cursor next.floor :=
    ⟨table.valid, half, by rw [memoryEq]; exact post.header, post.occupied, table.power,
      heap.trans table.heap, table.bounded, table.aligned, table.earlier, table.lower⟩
  have readerTable (reader : ι) (different : reader ≠ writer) :
      TableState target (objects reader).kind (objects reader).plan (objects reader).slots cursor (objects reader).floor := by
    have readerTable := family.tables reader
    obtain ⟨header, occupied⟩ := post.other_model table.valid (objects reader).kind (objects reader).plan readerTable.valid
      (family.apart writer reader (Ne.symm different)) (objects reader).slots readerTable.header readerTable.occupied
    exact ⟨readerTable.valid, readerTable.half, header, occupied, readerTable.power,
      heap.trans readerTable.heap, readerTable.bounded, readerTable.aligned, readerTable.earlier, readerTable.lower⟩
  have nextFamily : Model target cursor (Function.update objects writer next) := by
    constructor
    · intro index
      by_cases same : index = writer
      · subst index
        simpa only [Function.update_self] using writerTable
      · simpa only [Function.update_of_ne same] using readerTable index same
    · intro first second different
      have plans (index : ι) : (Function.update objects writer next index).plan = (objects index).plan := by
        by_cases same : index = writer
        · subst index; rw [Function.update_self]
        · rw [Function.update_of_ne same]
      have kinds (index : ι) : (Function.update objects writer next index).kind = (objects index).kind := by
        by_cases same : index = writer
        · subst index; rw [Function.update_self]
        · rw [Function.update_of_ne same]
      simpa only [Apart, plans, kinds] using family.apart first second different
  refine ⟨paid, next, bounded, fits, clock, rfl, rfl, rfl, nextFamily, ?_,
    post.count_bound.1, post.count_bound.2, locals, globals, codes,
    environment.of_fields codes domain endian, (fun address outside => post.protected_word address outside),?_⟩
  · intro index
    by_cases same : index = writer
    · subst index; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne same]

  · intro index
    by_cases same : index=writer
    · subst index
      simpa only [Function.update_self] using writerValues
    · change Get.OccupiedValuesHave target (cell (Function.update objects writer next index).plan .values 0)
        (BitVec.ofNat 64 (Function.update objects writer next index).plan.capacity) (Function.update objects writer next index).slots (property index)
      rw [Function.update_of_ne same]
      apply (values index).of_agreement source target _ _ _ _
      intro slot inside occupied
      have valid := (family.tables index).valid
      have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (capacity_small (objects index).kind _ valid)]
      rw [capNumber] at inside
      rw [scaled_cell,memoryEq]
      exact TableFootprint.Frame.other_pools source.memory memory old.kind (objects index).kind old.plan (objects index).plan table.valid valid
        (family.apart writer index (Ne.symm same)) post.footprint .values _ (word_offset_inside (objects index).kind _ .values slot.toNat (Or.inl rfl) inside)

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.delete_normal_values
